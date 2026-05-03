"""
Processes FOL formulae to ensure correct format for tokeniser

"""

import re    # for regex


def remove_whitespaces(my_str):
    my_str = my_str.replace('\n','')    # remove newlines
    my_str = my_str.replace('\t','')    # remove tabs
    my_str = re.sub(r'\s+','', my_str)    # remove multiple whitespaces
    return my_str.strip()


def extract_formulas(filename):
    # load file
    with open(filename,"r") as f:
        txt = f.read()

    # fix negation: : from ¬A to (¬A)
    txt = re.sub(r'¬\s*([A-Za-z][A-Za-z0-9_]*\s*\([^)]*\)|[A-Za-z][A-Za-z0-9_]*)', r'(¬\1)', txt)

    txt = txt.splitlines()

    txt = [remove_whitespaces(line) for line in txt]

    return txt
