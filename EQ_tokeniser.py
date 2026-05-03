"""
mappings:

    # logical connectives
    '→','=>': "Implication",
    '¬','~': "Negation",
    '∧','&': "And",
    '∨','|': "Or",

    # quantifiers
    '∀','!': "ForAll",
    '∃','?': "Exists",

    # punctuation
    '(': "LParen",
    ')': "RParen",
    '[': "LBracket",
    ']': "RBracket",
    ':': "Colon",
    ',': "Comma",

    # literals
    '$true': "True",
    '$false': "False",

    [X, Y] = variable list
    :      = separate quantifier from body
    ()     = group
    lowercase words = atoms/predicates
    uppercase words = variables
    f(args) : predicate
"""


def tokenise(formula, is_tptp=False):
    # converts formula into a list of tokens
    tokens = []
    i = 0
    formula = formula.strip()
    len_formula = len(formula)

    single_char_tokens = {
        # logical connectives
        '→': "Implication",
        '¬': "Negation",
        '~': "Negation",
        '∧': "And",
        '&': "And",
        '∨': "Or",
        '|': "Or",
        # quantifiers
        '∀': "ForAll",
        '!': "ForAll",
        '∃': "Exists",
        '?': "Exists",
        # punctuation
        '(': "LParen",
        ')': "RParen",
        '[': "LBracket",
        ']': "RBracket",
        ':': "Colon",
        ',': "Comma",
    }

    while i < len_formula:

        # check for '=>' first since it is multi-character
        if formula[i:i+2] == '=>':
            tokens.append(('Implication', formula[i:i+2]))
            i += 2

        # check for single-character tokens
        elif formula[i] in single_char_tokens:
            tokens.append((single_char_tokens[formula[i]], formula[i]))
            i += 1

        # check for literals
        elif formula[i] == '$':
            if formula[i:i+5] == '$true':
                tokens.append(('True', formula[i:i+5]))
                i += 5
            elif formula[i:i+6] == '$false':
                tokens.append(('False', formula[i:i + 6]))
                i += 6

        # is another word
        elif formula[i].isalpha() or formula[i] == '_':
            word = formula[i]
            if is_tptp:
                if formula[i].isupper():
                    tokens.append(('Variable', word))
                else:
                    tokens.append(('Symbol', word))
            else:   # for equations
                if formula[i].islower():
                    tokens.append(('Variable', word))
                else:    # token or predicate: Prerequisite: must be lower-case
                    tokens.append(('Symbol', word))
            i += 1

        else:    # handle unknown
            print("WARNING: Unknown character",formula[i], "at position", i)
            i += 1
            continue

    return tokens
