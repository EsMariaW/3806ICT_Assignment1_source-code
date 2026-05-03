"""
Parses EQ formulae

    Operator precedence:
        implication
        or
        and
        forall, exists

    Structures:

        Implication:
        {
            'kind': 'Implication'
            'left': {}    <-- LHS of implication
            'right': {}    <-- RHS of implication
        }

        Negation:
        {
            'kind': 'Negation'
            'body': {}    <-- element to be negated
        }

        And:
        {
            'kind': 'And'
            'args': []    <-- list of elements to be ANDed together
        }

        Or:
        {
            'kind': 'Or'
            'args': []    <-- list of elements to be ORed together
        }

        ForAll:
        {
            'kind': 'ForAll'
            'var': ''    <-- variable it applies to
            'body': {}    <-- body that variable is applied in
        }

        Exists:
        {
            'kind': 'Exists'
            'var': ''    <-- variable it applies to
            'body': {}    <-- body that variable is applied in
        }

        True:
        {
            'kind': 'True'
        }

        False:
        {
            'kind': 'False'
        }

        Var
        {
            'kind': 'Var'
            'name': ''    <-- name of variable; uppercase
        }

        Symbol: can be either:

            Const
            {
                'kind': 'Const'
                'name': ''    <-- name of constant; lowercase with no arguments
            }

            Pred
            {
                'kind': 'Pred'
                'name': ''    <-- name of function
                'args': []    <-- list of arguments for predicate
            }
"""


def and_parser(tokens, current_idx):
    left, current_idx = formula_unit_parser(tokens, current_idx)
    args = [left]
    while current_idx < len(tokens) and tokens[current_idx][0] == 'And':
        current_idx += 1  # skip And symbol
        arg, current_idx = formula_unit_parser(tokens, current_idx)
        args.append(arg)
    if len(args) == 1:
        return args[0], current_idx  # return element instead of single-element list
    return {
        'kind': 'And',
        'args': args
    }, current_idx


def or_parser(tokens, current_idx):
    left, current_idx = and_parser(tokens, current_idx)
    args = [left]
    while current_idx < len(tokens) and tokens[current_idx][0] == 'Or':
        current_idx += 1  # skip Or symbol
        arg, current_idx = and_parser(tokens, current_idx)
        args.append(arg)
    if len(args) == 1:
        return args[0], current_idx  # return element instead of single-element list
    return {
        'kind': 'Or',
        'args': args
    }, current_idx


def symbol_parser(tokens, current_idx):
    symbol_name = tokens[current_idx][1]
    current_idx += 1
    if current_idx < len(tokens) and tokens[current_idx][0] == 'LParen':  # is Pred
        current_idx += 1
        args, current_idx = args_parser(tokens, current_idx)  # get all the arguments between the parentheses
        current_idx += 1
        return {
            'kind': 'Pred',
            'name': symbol_name,
            'args': args
        }, current_idx
    # if not Pred, then Symbol is Const
    return {
        'kind': 'Const',
        'name': symbol_name
    }, current_idx


def args_parser(tokens, current_idx):
    # parses the arguments of a predicate
    args = []
    while tokens[current_idx][0] != 'RParen':
        # if the argument is a variable
        if tokens[current_idx][0] == 'Variable':
            args.append({
                'kind': 'Var',
                'name': tokens[current_idx][1]
            })
            current_idx += 1
        # if the argument is another symbol (const/func)
        elif tokens[current_idx][0] == 'Symbol':
            arg, current_idx = symbol_parser(tokens, current_idx)
            args.append(arg)
        # if there is a comma, ignore
        if tokens[current_idx][0] == 'Comma':
            current_idx += 1
    return args, current_idx  # current_idx now pointing at a RParen


def vars_parser(tokens, current_idx):
    vars = []
    while tokens[current_idx][0] != 'RBracket':
        if tokens[current_idx][0] == 'Variable':
            vars.append(tokens[current_idx][1])
            current_idx += 1
        if tokens[current_idx][0] == 'Comma':
            current_idx += 1
    return vars, current_idx


def formula_unit_parser(tokens, current_idx):
    current_token_label = tokens[current_idx][0]

    if current_token_label == 'LParen':  # starting another fomula
        current_idx += 1  # skip LParen symbol
        betw_parentheses, current_idx = formula_parser(tokens, current_idx)
        current_idx += 1  # skip RParen symbol
        return (betw_parentheses, current_idx)

    if current_token_label == 'True':
        return {
            'kind': 'True'
        }, current_idx + 1  # skip True symbol

    if current_token_label == 'False':
        return {
            'kind': 'False'
        }, current_idx + 1  # skip False symbol

    if current_token_label == 'Negation':
        current_idx += 1  # skip Negation symbol
        body, current_idx = formula_unit_parser(tokens, current_idx)
        return {
            'kind': 'Negation',
            'body': body
        }, current_idx

    if current_token_label == 'ForAll':  # ![variables]:body
        current_idx += 1  # ForAll
        vars = tokens[current_idx][1]
        current_idx += 1  # skip Variable symbol
        body, current_idx = formula_unit_parser(tokens, current_idx)
        # to nest multiple vars, e.g. Forall(X, Forall(Y)) put Y (seen last) inside X
        for var in reversed(vars):
            body = {
                'kind': 'ForAll',
                'var': var,
                'body': body
            }
        return body, current_idx

    if current_token_label == 'Exists':  # ?[variables]:body
        current_idx += 1  # Exists
        vars = tokens[current_idx][1]
        current_idx += 1  # skip Variable symbol
        body, current_idx = formula_unit_parser(tokens, current_idx)
        # to nest multiple vars, e.g. Exists(X, Exists(Y))  put Y (seen last) inside X
        for var in reversed(vars):
            body = {
                'kind': 'Exists',
                'var': var,
                'body': body
            }
        return body, current_idx

    if current_token_label == 'Symbol':
        return symbol_parser(tokens, current_idx)

    raise ValueError(f"Unexpected token: {tokens[current_idx]}")


def formula_parser(tokens, current_idx):
    left, current_idx = or_parser(tokens, current_idx)
    if current_idx < len(tokens) and tokens[current_idx][0] == 'Implication':
        current_idx += 1  # skip Implication symbol
        right, current_idx = formula_parser(tokens, current_idx)
        return {
            'kind': 'Implication',
            'left': left,
            'right': right
        }, current_idx
    return left, current_idx


def parse(tokens):
    return formula_parser(tokens, 0)[0]

