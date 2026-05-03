"""
Python Implementation of this pseudocode:

    Data: A first-order logic formula A.
    Result: A derivation tree in L K ′
    .
    build the bottom sequent ⊢ A;

    foreach top sequent on an open branch do
        if any of the rules i d, ⊤R and ⊥L is applicable then
            apply the rule backwards and close the branch;
        else if any of the rules ∧L, ∨R, → R,¬L,¬R, ∀R and ∃L then
            apply the rule backwards;
        else if any of the rules ∧R, ∨L and → L is applicable then
            apply the rule backwards and create a new branch;
        else if ∀L or ∃R is applicable and there is a term t which has not been used to instantiate the quantified variable x in said formula then
            apply the rule backwards by substituting x with t;
        else if ∀L or ∃R is applicable then
            apply the rule backwards and create a fresh term;
        else
            stop;
        end
    end
"""

fresh_counter = 0


def sides_equal(a, b):
    if a['kind'] != b['kind']:
        return False
    if a['kind'] == 'Pred':
        if (a['name'] != b['name']) or (len(a['args']) != len(b['args'])):    # check same predicate name, check arguments
            return False
        return all(sides_equal(x, y) for x, y in zip(a['args'], b['args']))    # check each x,y pair are equal
    if a['kind'] in ('Var', 'Const'):
        return a['name'] == b['name']
    return False


def fresh_term():
    global fresh_counter
    term_name = f"f{fresh_counter}"
    fresh_counter += 1
    return {'kind': 'Const', 'name': term_name}


def get_terms(formulas):
    terms = []

    def traverse(formula):    # inner function to traverse branches
        kind = formula['kind']
        if kind in ('Var', 'Const'):
            terms.append(formula)
        elif kind in ('And', 'Or', 'Pred'):
            for this_arg in formula['args']:
                traverse(this_arg)
        elif kind in ('Negation', 'ForAll', 'Exists'):
            traverse(formula['body'])
        elif kind == 'Implication':
            traverse(formula['left'])
            traverse(formula['right'])

    for this_formula in formulas:
        traverse(this_formula)

    return terms if terms else [fresh_term()]


def sub(formula, var, term):
    # to replace variable var with term throughout the formula

    kind = formula['kind']

    if kind == 'Var':
        if formula['name'] == var:    # same variable name
            return term
        else:
            return formula    # to return variables that are not a match

    if kind == 'Pred':
        return {
            'kind': 'Pred',
            'name': formula['name'],
            'args': [sub(this_arg, var, term) for this_arg in formula['args']]
        }

    if kind == 'Negation':
        return {
            'kind': 'Negation',
            'body': sub(formula['body'], var, term)
        }

    if kind in ('And', 'Or'):
        return {
            'kind': kind,
            'args': [sub(this_arg, var, term) for this_arg in formula['args']]
        }

    if kind == 'Implication':
        return {
            'kind': 'Implication',
            'left': sub(formula['left'], var, term),
            'right': sub(formula['right'], var, term),
        }

    if kind in ('ForAll', 'Exists'):
        if formula['var'] == var:
            return formula
        return {
            'kind': kind,
            'var': formula['var'],
            'body': sub(formula['body'], var, term)
        }

    return formula    # True, False, Const


def base_algor2(sequent):

    try:

        left_seq = sequent['left'] or []
        right_seq = sequent['right'] or []

        # print('\n\n')
        # print(left_seq)
        # print()
        # print(right_seq)

        """
        if any of the rules id, ⊤R and ⊥L is applicable then
            apply the rule backwards and close the branch
        """

        """
        id
            premise:    
            sequent:    𝛤,A ⊦ A,𝛥
        """
        for l in left_seq:
            for r in right_seq:
                if sides_equal(l, r):
                    #print("Trying ID")
                    #print("id", " | ", left_seq, "⊢", right_seq)
                    return 'closed'

        """
        ⊤R
            premise:    
            sequent:    𝛤 ⊦ ⊤,𝛥
        """
        if any(r['kind'] =='True' for r in right_seq):
            #print("Trying True Right")
            #print("⊤R", " | ", left_seq, "⊢", right_seq)
            return 'closed'

        """
        ⊥L
            premise:    
            sequent:    𝛤,⊥ ⊦ 𝛥
        """
        if any(l['kind'] == 'False' for l in left_seq):
            #print("Trying False Left")
            #print("⊥L", " | ", left_seq, "⊢", right_seq)
            return 'closed'

        """
        else if any of the rules ∧L, ∨R, →R,¬L,¬R, ∀R and ∃L then
            apply the rule backwards;
        """

        """
        ∧L
            premise:    𝛤,A,B ⊦ 𝛥
            sequent:    𝛤,A∧B ⊦ 𝛥
        """
        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'And':
                #print("Trying And Left")
                #print("∧L", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq[:index] + formula['args'] + left_seq[index+1:],
                    'right': right_seq
                })
                if result == 'closed':
                    return 'closed'

        """
        ¬L
            premise:       𝛤 ⊦ A,𝛥
            sequent:    𝛤,¬A ⊦ 𝛥
        """
        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'Negation':
                #print("Trying Negation Left")
                #print("¬L", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq[:index] + left_seq[index+1:],
                    'right': [formula['body']] + right_seq
                })
                if result == 'closed':
                    return 'closed'

        """
        ¬R
            premise:    𝛤,A ⊦ 𝛥 
            sequent:      𝛤 ⊦ ¬A,𝛥
        """
        for index, formula in enumerate(right_seq):
            if formula['kind'] == 'Negation':
                #print("Trying Negation Right")
                #print("¬R", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq + [formula['body']],
                    'right': right_seq[:index] + right_seq[index+1:]
                })
                if result == 'closed':
                    return 'closed'

        """
        ∨R
            premise:    𝛤 ⊦ A,B,𝛥
            sequent:    𝛤 ⊦ A∨B,𝛥
        """
        for index, formula in enumerate(right_seq):
            if formula['kind'] == 'Or':
                #print("Trying Or Right")
                #print("∨R", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq,
                    'right': right_seq[:index] + formula['args'] + right_seq[index+1:]
                })
                if result == 'closed':
                    return 'closed'

        """
        ∀R
            premise:    𝛤 ⊦ A[a/x],𝛥    <-- fresh variable
            sequent:    𝛤 ⊦ ∀x.A,𝛥
        """
        for index, formula in enumerate(right_seq):
            if formula['kind'] == 'ForAll':
                #print("Trying ForAll Right")
                #print("∀R", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq,
                    'right': right_seq[:index] + [sub(formula['body'], formula['var'], fresh_term())] + right_seq[index+1:]
                })
                if result == 'closed':
                    return 'closed'

        """
        ∃L
            premise:    𝛤,A[a/x] ⊦ 𝛥
            sequent:      𝛤,∃x.A ⊦ 𝛥
        """
        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'Exists':
                #print("Trying Exists Left")
                #print("∃L", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq[:index] + [sub(formula['body'], formula['var'], fresh_term())] + left_seq[index+1:],
                    'right': right_seq
                })
                if result == 'closed':
                    return 'closed'

        """
        →R
            premise:    𝛤,A ⊦ B,𝛥
            sequent:      𝛤 ⊦ A→B,𝛥
        """
        for index,formula in enumerate(right_seq):
            if formula['kind'] == 'Implication':
                #print("Trying Implication Right")
                #print("→R", " | ", left_seq, "⊢", right_seq)
                result = base_algor2({
                    'left': left_seq + [formula['left']],
                    'right': right_seq[:index] + [formula['right']] + right_seq[index+1:]
                })
                if result == 'closed':
                    return 'closed'

        """
        else if any of the rules ∧R, ∨L and → L is applicable then
            apply the rule backwards and create a new branch;
        """

        """
        ∧R
            premise:    𝛤 ⊦ A,𝛥      𝛤 ⊦ B,𝛥
            sequent:    𝛤 ⊦ A∧B,𝛥
        """
        for index, formula in enumerate(right_seq):
            if formula['kind'] == 'And':
                #print("Trying And Right")
                #print("∧R", " | ", left_seq, "⊢", right_seq)
                branches = [base_algor2({
                    'left': left_seq,
                    'right': right_seq[:index] + [this_arg] + right_seq[index+1:]
                }) for this_arg in formula['args']]
                return 'closed' if all(branch == 'closed' for branch in branches) else 'open'

        """
        ∨L
            premise:    𝛤,A ⊦ 𝛥      𝛤,B ⊦ 𝛥
            sequent:    𝛤,A∨B ⊦ 𝛥
        """
        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'Or':
                #print("Trying Or Left")
                #print("∨L", " | ", left_seq, "⊢", right_seq)
                branches = [base_algor2({
                    'left': left_seq[:index] + [this_arg] + left_seq[index+1:],
                    'right': right_seq
                }) for this_arg in formula['args']]
                return 'closed' if all(branch == 'closed' for branch in branches) else 'open'

        """
        →L
            premise:    𝛤 ⊦ A,𝛥      𝛤,B ⊦ 𝛥
            sequent:    𝛤,A→B ⊦ 𝛥
        """
        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'Implication':
                #print("Trying Implication Left")
                #print("→L", " | ", left_seq, "⊢", right_seq)
                branch1 = base_algor2({
                    'left': left_seq[:index] + left_seq[index+1:],
                    'right': [formula['left']] + right_seq
                })
                branch2 = base_algor2({
                    'left': left_seq[:index] + [formula['right']] + left_seq[index + 1:],
                    'right': right_seq
                })
                return 'closed' if branch1 == 'closed' and branch2 == 'closed' else 'open'

        """
        else if ∀L or ∃R is applicable and there is a term t which has not been used to instantiate the quantified variable x in said formula then
            apply the rule backwards by substituting x with t;
        else if ∀L or ∃R is applicable then
            apply the rule backwards and create a fresh term;
        """

        terms = get_terms(left_seq + right_seq)

        """
        ∀L
            premise:    𝛤,∀x.A,A[t/x] ⊦ 𝛥
            sequent:    𝛤,∀x.A ⊦ 𝛥
        """

        for index, formula in enumerate(left_seq):
            if formula['kind'] == 'ForAll':
                #print("Trying ForAll Left tracking terms")
                #print("∀L", " | ", left_seq, "⊢", right_seq)
                for term in terms:
                    result = base_algor2({
                        'left': left_seq[:index] + [sub(formula['body'], formula['var'], term)] + left_seq[index + 1:],
                        'right': right_seq
                    })
                    if result == 'closed':
                        return 'closed'
                result = base_algor2({
                    'left': left_seq[:index] + [sub(formula['body'], formula['var'], fresh_term())] + left_seq[index + 1:],
                    'right': right_seq
                })
                if result == 'closed':
                    return 'closed'

        """
        ∃R
            premise:    𝛤 ⊦ ∃x.A,A[t/x],𝛥
            sequent:    𝛤 ⊦ ∃x.A,𝛥
        """
        for index, formula in enumerate(right_seq):
            if formula['kind'] == 'Exists':
                #print("Trying Exists Right tracking terms")
                #print("∃R", " | ", left_seq, "⊢", right_seq)
                for term in terms:
                    result = base_algor2({
                        'left': left_seq,
                        'right': right_seq[:index] + [sub(formula['body'], formula['var'], term)] + right_seq[index + 1:]
                    })
                    if result == 'closed':
                        return 'closed'
                result = base_algor2({
                        'left': left_seq,
                        'right': right_seq[:index] + [sub(formula['body'], formula['var'], fresh_term())] + right_seq[index + 1:]
                    })
                if result == 'closed':
                    return 'closed'

        return 'open'

    except RecursionError:
        return 'open'
