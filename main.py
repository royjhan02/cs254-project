import ollama
from ollama import chat, ChatResponse
import sys
import subprocess
import re

def main():
    if len(sys.argv) < 3:
        print("Usage: python3 main.py <path to program file> <model>")
        return
    
    program_path = sys.argv[1]
    model = sys.argv[2]

    with open(program_path, 'r') as program_file:
        program = program_file.read()

    # Pull the model
    ollama.pull(model)

    messages = [
        {
            'role': 'user',
            'content': program,
        },
    ]

    it = 0

    while True:
        response: ChatResponse = chat(model=model, messages=messages)

        # Write the response content to an SMT file
        smt_file = f"discovery-{it}.smt2"
        with open(smt_file, 'w') as f:
            f.write(response.messages[-1].content)
        
        # Run z3 on the SMT file
        result = subprocess.run(["z3", smt_file], capture_output=True, text=True)
        output = result.stdout.strip()
        statuses = re.findall(r"^(sat|unsat|unknown)", output, re.MULTILINE)
        print("Status results:", statuses)

        if statuses and all(status == "sat" for status in statuses):
            print(f"Iteration {it}: Both the invariant and termination checks are satisfied.")
            break
        else:
            print(f"Iteration {it}: The checks were not fully satisfied, iterating.")

        # Use the response content directly instead of re-reading the file
        file_content = response.messages[-1].content

        messages += [
            {'role': 'assistant', 'content': file_content},
            {'role': 'user', 'content': output},
        ]

        it += 1

    print(f"Solved in {it} iterations.")
    print(f"Final result:\n{output}")

if __name__ == "__main__":
    main()
