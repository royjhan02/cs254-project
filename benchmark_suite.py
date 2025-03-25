import argparse
import time
import subprocess
import re
import ollama
from ollama import chat, ChatResponse

def clean_smt_content(content):
    """
    Clean the given SMT-LIB content by keeping only lines that either:
      - Are empty (or contain only whitespace), or
      - Start (after leading whitespace) with '(' or ';'.
    This preserves the original vertical spacing only for truly empty lines.
    """
    cleaned_lines = []
    for line in content.splitlines():
        # Preserve truly empty lines
        if line.strip() == "" and len(cleaned_lines) > 0:
            cleaned_lines.append(line)
        # Otherwise, keep only lines starting with '(' or ';'
        elif line.lstrip().startswith('(') or line.lstrip().startswith(';'):
            cleaned_lines.append(line)
    return "\n".join(cleaned_lines)

def run_smt_invariant_loop(program, model, bench_name):
    """
    Run the iterative SMT synthesis loop for a given synthetic loop.
    Returns the number of iterations taken, total time, and final SMT solver output.
    """
    messages = [{'role': 'user', 'content': program}]
    it = 0
    start_time = time.perf_counter()

    while True:
        response: ChatResponse = chat(model=model, messages=messages)
        # Use response.message.content to extract SMT content
        original_content = response.message.content
        cleaned_content = clean_smt_content(original_content)
        
        # Save the candidate SMT file for debugging/inspection.
        smt_file = f"{bench_name}-discovery-{it}.smt2"
        with open(smt_file, 'w') as f:
            f.write(cleaned_content)
        
        # Run Z3 on the SMT file.
        result = subprocess.run(["z3", smt_file], capture_output=True, text=True)
        output = result.stdout.strip()
        statuses = re.findall(r"^(sat|unsat|unknown)", output, re.MULTILINE)
        print(f"[{bench_name}] Iteration {it} status: {statuses}")

        # Save Z3 output to a file for inspection.
        z3_file = f"{bench_name}-z3-{it}.txt"
        with open(z3_file, 'w') as z3f:
            z3f.write(result.stdout + "\n" + result.stderr)

        # If all statuses are "sat", consider the verification successful.
        if statuses and all(status == "sat" for status in statuses):
            break

        # Update the conversation with the assistant's SMT file and Z3 output.
        messages += [
            {'role': 'assistant', 'content': cleaned_content},
            {'role': 'user', 'content': output},
        ]
        it += 1

    end_time = time.perf_counter()
    duration = end_time - start_time
    return it, duration, output

def run_benchmark_suite(model):
    """
    Runs a suite of synthetic loop benchmarks and prints a summary of performance.
    """
    # Extended list of synthetic loop benchmarks.
    benchmarks = [
        {
            "name": "SimpleLinear",
            "program": """x = 10;
while (x > 0) {
    x = x - 1;
}"""
        },
        {
            "name": "MultiVariable",
            "program": """x = 10; y = 20;
while (x > 0 && y > 0) {
    x = x - 1;
    y = y - 2;
}"""
        },
        {
            "name": "PolynomialUpdate",
            "program": """x = 100;
while (x > 1) {
    x = x - (x/2);
}"""
        },
        {
            "name": "NestedLoop",
            "program": """i = 0; j = 0;
while (i < 10) {
    while (j < 5) {
        j = j + 1;
    }
    i = i + 1;
    j = 0;
}"""
        },
        {
            "name": "ConditionalLoop",
            "program": """x = 10;
while (x > 0) {
    if (x % 2 == 0) {
        x = x - 2;
    } else {
        x = x - 1;
    }
}"""
        },
        {
            "name": "ExponentialDecayLoop",
            "program": """x = 100;
while (x > 1) {
    x = x / 2;
}"""
        }
    ]

    print("Using model:", model)
    # Only pull the model if it's not your custom model that is already created.
    if model != "cs254":
        ollama.pull(model)

    results = {}
    for bench in benchmarks:
        print(f"\nRunning benchmark: {bench['name']}")
        iterations, duration, final_output = run_smt_invariant_loop(bench["program"], model, bench["name"])
        results[bench["name"]] = {
            "iterations": iterations,
            "time_seconds": duration,
            "final_output": final_output
        }
        print(f"Benchmark {bench['name']} solved in {iterations} iterations, time: {duration:.2f} seconds.\n")
    
    print("Benchmark suite results:")
    for name, res in results.items():
        print(f" - {name}: {res['iterations']} iterations, {res['time_seconds']:.2f} seconds")
    return results

def main():
    parser = argparse.ArgumentParser(
        description="Extended SMT Invariant Synthesis Benchmark Suite for Synthetic Loops"
    )
    parser.add_argument("--model", default="cs254",
                        help="Name of the model to use (default: cs254)")
    args = parser.parse_args()
    run_benchmark_suite(args.model)

if __name__ == "__main__":
    main()
