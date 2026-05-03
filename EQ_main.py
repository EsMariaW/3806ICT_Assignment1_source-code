"""
Code used to run EQ experiments
    Note: relies on EQ_fol_diverse.txt being available
"""

import json
import time
from multiprocessing import Process, Queue

import EQ_tokeniser
import EQ_preprocess_formulas
import EQ_parser
import A_base_algor2
import A_improved_algor2

def worker(q, func, args):
    try:
        result = func(*args)
        q.put(result)
    except Exception as e:
        q.put(e)


def run_with_timeout(func, args=(), timeout=5):
    q = Queue()

    p = Process(target=worker, args=(q, func, args))
    p.start()
    p.join(timeout)

    if p.is_alive():
        p.terminate()
        p.join()
        return "timeout"
    else:
        return q.get() if not q.empty() else None


# ------------------ Base Algorithm ------------------

if __name__ == "__main__":
    formulas = EQ_preprocess_formulas.extract_formulas("EQ_fol_diverse.txt")

    line_num = 1
    closed_count = 0
    open_count = 0
    timeout_count = 0

    total_start_time = time.perf_counter()

    for form in formulas:
        if form:
            # print(form)
            tokenised_formula = EQ_tokeniser.tokenise(form)
            #print(json.dumps(tokenised_formula,indent=2))
            parsed_formula = EQ_parser.parse(tokenised_formula)
            #print(json.dumps(parsed_formula,indent=2))
            sequent = {
                'left': [],
                'right': [parsed_formula]
            }
            #print(sequent)

            solve_start = time.perf_counter()
            result = run_with_timeout(A_base_algor2.base_algor2, args=(sequent,), timeout=20)
            solve_total = time.perf_counter() - solve_start

            if result == 'closed':
                closed_count += 1
                print(f"{line_num} :   {result}       {solve_total:.3f}s    {form}")
            if result == 'open':
                open_count += 1
                print(f"{line_num} :   {result}         {solve_total:.3f}s    {form}")
            if result == "timeout":
                timeout_count += 1
                print(f"{line_num} :   timed out   {solve_total:.3f}s    {form}")

            line_num += 1

    total_time = time.perf_counter() - total_start_time

    print()
    print("=" * 60)
    print(f"Total time:      {total_time:.3f}s")
    print(f"Total formulas:  {line_num - 1}")
    print(f"  Closed:        {closed_count}")
    print(f"  Open:          {open_count}")
    print(f"  Timed out:     {timeout_count}")
    print("=" * 60)
    print()


# ---------------- Improved Algorithm ----------------

# if __name__ == "__main__":
#     formulas = EQ_preprocess_formulas.extract_formulas("EQ_fol_diverse.txt")

#     line_num = 1
#     closed_count = 0
#     open_count = 0
#     timeout_count = 0

#     total_start_time = time.perf_counter()

#     for form in formulas:
#         if form:
#             # print(form)
#             tokenised_formula = EQ_tokeniser.tokenise(form)
#             #print(json.dumps(tokenised_formula,indent=2))
#             parsed_formula = EQ_parser.parse(tokenised_formula)
#             #print(json.dumps(parsed_formula,indent=2))
#             sequent = {
#                 'left': [],
#                 'right': [parsed_formula]
#             }
#             #print(sequent)

#             solve_start = time.perf_counter()
#             result = run_with_timeout(A_improved_algor2.improved_algor2, args=(sequent,), timeout=20)
#             solve_total = time.perf_counter() - solve_start

#             if result == 'closed':
#                 closed_count += 1
#                 print(f"{line_num} :   {result}       {solve_total:.3f}s    {form}")
#             if result == 'open':
#                 open_count += 1
#                 print(f"{line_num} :   {result}         {solve_total:.3f}s    {form}")
#             if result == "timeout":
#                 timeout_count += 1
#                 print(f"{line_num} :   timed out   {solve_total:.3f}s    {form}")

#             line_num += 1

#     total_time = time.perf_counter() - total_start_time

#     print()
#     print("=" * 60)
#     print(f"Total time:      {total_time:.3f}s")
#     print(f"Total formulas:  {line_num - 1}")
#     print(f"  Closed:        {closed_count}")
#     print(f"  Open:          {open_count}")
#     print(f"  Timed out:     {timeout_count}")
#     print("=" * 60)
#     print()
