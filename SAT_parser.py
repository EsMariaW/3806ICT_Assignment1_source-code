"""
Parses unsatisfiable SAT CNF problems
    Applies DeMorgan's law to convert CNF to DNF to reduce branching
        (because:
            unsatisfiable SAT CNF |- False
            ~ (unsatisfiable SAT CNF) |- True
            unsatisfiable SAT DNF |- True
        )

    Var
    {
        'kind': 'Var'
        'name': ''    <-- name of variable; uppercase
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

"""

def parser(file_txt):

    dis = []

    for line in file_txt.splitlines():
        line = line.strip()

        if not line or line.startswith('p') or line.startswith('c'):    # skip comments and problem header
            continue

        con = []

        for symbol in line.split():

            if symbol == '0':    # skip end of clause character
                continue

            var = {
                'kind': 'Const',
                'name': 'x' + symbol.lstrip('-')    # e.g. convert to x65; -65 indicates it should be -x65
            }

            if symbol.startswith('-'):    # encapsulate variable with negation
                con.append(
                    {
                        'kind': 'Negation',
                        'body': var
                    }
                )
            else:
                con.append(var)

        if len(con) == 1:
            dis.append(con[0])
        else:    # have multiple clauses to perform conunction
            dis.append(
                {
                    'kind': 'And',
                    'args': con
                }
            )

    return dis[0] if len(dis) == 1 else dis
