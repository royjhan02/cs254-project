from ollama import chat, ChatResponse
import sys
import subprocess
import re
import os
from datetime import datetime
import time

def clean_smt_content(content):
    """
    Clean the given SMT-LIB content by keeping only lines that either:
      - Are empty (or contain only whitespace), or
      - Start (after leading whitespace) with '(' or ';'.
    This preserves the original vertical spacing only for truly empty lines.

    Args:
        content: A string containing the SMT-LIB file content.

    Returns:
        A cleaned string with valid SMT-LIB lines and only original blank lines.
    """
    cleaned_lines = []
    for line in content.splitlines():
        # If the line is empty (or only whitespace), preserve it.
        if line.strip() == "" and len(cleaned_lines) > 0:
            cleaned_lines.append(line)
        # Otherwise, only keep lines starting with '(' or ';'
        elif line.lstrip().startswith('(') or line.lstrip().startswith(';'):
            cleaned_lines.append(line)
    return "\n".join(cleaned_lines)


def main():
    if len(sys.argv) < 3:
        print("Usage: python3 main.py <path to program file> <model>")
        return
    
    program_path = sys.argv[1]
    model = sys.argv[2]

    start = time.perf_counter()

    with open(program_path, 'r') as program_file:
        program = program_file.read()

    messages = [
        {
            'role': 'user',
            'content': program,
        },
    ]

    it = 0

    # Create directory for results
    dir_name = f"results/{datetime.now().strftime("%Y%m%d%H%M%S")}"
    os.makedirs(dir_name, exist_ok=True)

    # Create subdirectories for SMT and z3 files
    os.makedirs(os.path.join(dir_name, "uncleaned"), exist_ok=True)
    os.makedirs(os.path.join(dir_name, "discovery"), exist_ok=True)
    os.makedirs(os.path.join(dir_name, "z3"), exist_ok=True)

    while True:
        print(f"Beginning Iteration {it}")
        print(f"Iteration {it}: Generating SMT file...")
        response: ChatResponse = chat(model=model, messages=messages)
        print(f"Iteration {it}: SMT file generation complete.")

        # Write the response content to an SMT file
        smt_file = f"{dir_name}/discovery/discovery-{it}.smt2"
        uncleaned_smt_file = f"{dir_name}/uncleaned/uncleaned-{it}.smt2"
        original_content = response.message.content
        cleaned_content = clean_smt_content(original_content)

        with open(uncleaned_smt_file, 'w') as f:
            f.write(original_content)

        with open(smt_file, 'w') as f:
            f.write(cleaned_content)
        
        # Run z3 on the SMT file
        print(f"Iteration {it}: Running z3 on the SMT file...")
        result = subprocess.run(["z3", smt_file], capture_output=True, text=True)
        print(result)

        statuses = re.findall(r"^(sat|unsat|unknown)", result.stdout, re.MULTILINE)
        errors = re.findall(r"\berror\b", result.stdout, re.IGNORECASE)
        print(f"Iteration {it}: z3 status results:\n{statuses}")

        z3_file = f"{dir_name}/z3/z3-{it}.txt"
        results = result.stdout + "\n" + result.stderr
        with open(z3_file, 'w') as z3f:
            z3f.write(results)

        if statuses and all(status == "sat" for status in statuses) and len(statuses) > 1 and result.stderr == "" and not errors:
            print(f"Iteration {it}: Both the invariant and termination checks are satisfied.")
            break
        else:
            print(f"Iteration {it}: The checks were not fully satisfied, iterating.")

        messages += [
            {'role': 'assistant', 'content': cleaned_content},
            {'role': 'user', 'content': results},
        ]

        print(results)

        it += 1

    end = time.perf_counter()

    print(f"Final result:\n{result.stdout}")
    print(f"Solved in {it} iterations.")
    print(f"Total time taken: {end - start} seconds.")

if __name__ == "__main__":
    main()
