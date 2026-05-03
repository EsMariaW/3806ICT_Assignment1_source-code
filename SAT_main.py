import json
import time
import os

import SAT_parser
import A_base_algor2
import A_improved_algor2


directory = './SAT_Competition_2023_unsat/'

# ------------------ Base Algorithm ------------------

# ---------------- Improved Algorithm ----------------

if __name__ == "__main__":

    line_num = 1
    closed_count = 0
    open_count = 0
    aborted_count = 0
    closed_line_nums = set()
    open_line_nums = set()
    aborted_line_nums = set()

    active_threads = []

    total_start_time = time.perf_counter()

    for filename in sorted(os.listdir(directory)):  # sorted for reproducibility
        if filename.endswith('.cnf'):
            file_path = os.path.join(directory, filename)

            with open(file_path, 'r') as f:
                file_txt = f.readlines()
                num_rows = len(file_txt)
                print(f"{line_num} :  rows: {num_rows}      ", end="")
            if num_rows > 20000000:
                print(f"Aborted; too many rows: {num_rows}")
                aborted_count += 1
                aborted_line_nums.add(line_num)
                continue

            with open(file_path, 'r') as f:
                file_txt = f.read()

            print("Starting to Parse...       ", end="")
            parsed_formula = SAT_parser.parser(file_txt)

            sequent = {
                'left': [{
                    'kind': 'Or',
                    'args': parsed_formula
                }],
                'right': [
                    {'kind': 'True'}
                ]
            }

            print("Starting to Solve...       ", end="")

            try:
                solve_start = time.perf_counter()
                result = A_base_algor2.base_algor2(sequent)
                solve_total = time.perf_counter() - solve_start

                if result == 'closed':
                    closed_count += 1
                    closed_line_nums.add(line_num)
                    print(f" Result: {result}       Time: {solve_total:.3f}s")
                if result == 'open':
                    open_count += 1
                    open_line_nums.add(line_num)
                    print(f" Result: {result}       Time: {solve_total:.3f}s")

            except Exception as e:
                result = "error"
                print(f"{line_num} :   ERROR: {e}    {file_path}")

            line_num += 1

    total_time = time.perf_counter() - total_start_time

    print()
    print("=" * 60)
    print(f"Total time:      {total_time:.3f}s")
    print(f"Total formulas:  {line_num - 1 + aborted_count}")
    print(f"  Closed:        {closed_count}")
    print(f"  Open:          {open_count}")
    print(f"  Aborted:       {aborted_count}")
    print("=" * 60)
    print()


# ---------------- Improved Algorithm ----------------
#
# if __name__ == "__main__":
#
#     line_num = 1
#     closed_count = 0
#     open_count = 0
#     aborted_count = 0
#
#     active_threads = []
#
#     total_start_time = time.perf_counter()
#
#     for filename in sorted(os.listdir(directory)):    # sorted for reproducibility
#         if filename.endswith('.cnf'):
#             file_path = os.path.join(directory, filename)
#
#             with open(file_path, 'r') as f:
#                 file_txt = f.readlines()
#                 num_rows = len(file_txt)
#                 print(f"{line_num} :  rows: {num_rows}      ", end="")
#             if num_rows > 20000000:
#                 print(f"Aborted; too many rows: {num_rows}")
#                 aborted_count += 1
#                 continue
#
#
#             with open(file_path, 'r') as f:
#                 file_txt = f.read()
#
#             print("Starting to Parse...       ", end="")
#             parsed_formula = SAT_parser.parser(file_txt)
#
#             sequent = {
#                 'left': [{
#                     'kind': 'Or',
#                     'args': parsed_formula
#                 }],
#                 'right': [
#                     {'kind': 'True'}
#                 ]
#             }
#
#             print("Starting to Solve...       ", end="")
#
#             try:
#                 solve_start = time.perf_counter()
#                 result = A_improved_algor2.improved_algor2(sequent)
#                 solve_total = time.perf_counter() - solve_start
#
#                 if result == 'closed':
#                     closed_count += 1
#                     print(f" Result: {result}       Time: {solve_total:.3f}s")
#                 if result == 'open':
#                     open_count += 1
#                     print(f" Result: {result}       Time: {solve_total:.3f}s")
#
#             except Exception as e:
#                 result = "error"
#                 print(f"{line_num} :   ERROR: {e}    {file_path}")
#
#             line_num += 1
#
#
#
#     total_time = time.perf_counter() - total_start_time
#
#     print()
#     print("=" * 60)
#     print(f"Total time:      {total_time:.3f}s")
#     print(f"Total formulas:  {line_num - 1 + aborted_count}")
#     print(f"  Closed:        {closed_count}")
#     print(f"  Open:          {open_count}")
#     print(f"  Aborted:       {aborted_count}")
#     print("=" * 60)
#     print()
