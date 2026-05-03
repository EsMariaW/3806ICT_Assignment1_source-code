"""
Used to generate FOL formulae

"""
import random

# --------------------------------
# Vocabulary
# --------------------------------
PRED_U = ["P", "Q", "R", "S", "T", "U", "V", "W"]
PRED_B = ["F", "G", "H", "L", "M", "N", "K"]
VARS   = ["x", "y", "z", "w", "u"]

def rv():  return random.choice(VARS)
def ru():  return random.choice(PRED_U)
def rb():  return random.choice(PRED_B)
def rq():  return random.choice(["∀", "∃"])

# --------------------------------
# AST nodes
# --------------------------------
# Each node is a tuple whose first element is a tag string.
# Atoms:
#   ("atom", "P(x)")
# Connectives:
#   ("neg",   phi)
#   ("and",   phi, psi)
#   ("or",    phi, psi)
#   ("impl",  phi, psi)
# Quantifiers:
#   ("quant", "∀"/"∃", var, phi)

def Atom(pred, *args):
    return ("atom", f"{pred}({','.join(args)})")

def Neg(phi):
    return ("neg", phi)

def And(phi, psi):
    return ("and", phi, psi)

def Or(phi, psi):
    return ("or", phi, psi)

def Impl(phi, psi):
    return ("impl", phi, psi)

def Quant(q, var, phi):
    return ("quant", q, var, phi)

# --------------------------------
# Precedence (higher = tighter)
# --------------------------------
PREC = {"atom": 10, "neg": 9, "and": 7, "or": 6, "impl": 5, "quant": 4}

def prec(node):
    return PREC[node[0]]

def render(node, parent_tag=None, is_right=False):
    """
    Render AST to string, adding parentheses only when needed.
    Rules:
      - A child needs parens if its precedence is strictly lower than its parent's.
      - For right-associative → : left child needs parens if it has the same prec.
      - Quantifiers always parenthesize their body if the body is a connective,
        so scope is unambiguous.
    """
    tag = node[0]

    if tag == "atom":
        return node[1]

    if tag == "neg":
        body = node[1]
        inner = render(body, "neg")
        # Parens needed if body is a connective (not atom or neg)
        if body[0] not in ("atom", "neg"):
            inner = f"({inner})"
        return f"¬{inner}"

    if tag == "and":
        phi, psi = node[1], node[2]
        left  = render(phi, "and", is_right=False)
        right = render(psi, "and", is_right=True)
        if prec(phi) < prec(node):  left  = f"({left})"
        if prec(psi) < prec(node):  right = f"({right})"
        result = f"{left} ∧ {right}"

    elif tag == "or":
        phi, psi = node[1], node[2]
        left  = render(phi, "or", is_right=False)
        right = render(psi, "or", is_right=True)
        if prec(phi) < prec(node):  left  = f"({left})"
        if prec(psi) < prec(node):  right = f"({right})"
        result = f"{left} ∨ {right}"

    elif tag == "impl":
        phi, psi = node[1], node[2]
        # → is right-associative: left side needs parens if same precedence too
        left  = render(phi, "impl", is_right=False)
        right = render(psi, "impl", is_right=True)
        if prec(phi) <= prec(node):  left  = f"({left})"   # left of → always parenthesized if not tighter
        # right side: only parens if strictly lower (right-assoc gives it for free otherwise)
        # but since impl is the loosest connective, right rarely needs them
        if prec(psi) < prec(node):   right = f"({right})"
        result = f"{left} → {right}"

    elif tag == "quant":
        _, q, var, body = node
        inner = render(body, "quant")
        # Always wrap body in parens if it contains a connective, for clarity
        if body[0] not in ("atom", "neg", "quant"):
            inner = f"({inner})"
        return f"{q}{var} {inner}"

    # Wrap entire result in parens if needed by parent context
    if parent_tag is not None and prec(node) < PREC.get(parent_tag, 0):
        result = f"({result})"

    return result

# --------------------------------
# Formula builders (AST level)
# --------------------------------

def chain_impl(*parts):
    """Build right-associative implication chain: A → B → C → ..."""
    result = parts[-1]
    for p in reversed(parts[:-1]):
        result = Impl(p, result)
    return result

def forall(var, phi): return Quant("∀", var, phi)
def exists(var, phi): return Quant("∃", var, phi)
def Q(var, phi):      return Quant(rq(), var, phi)

# --------------------------------
# Easy formulas
# --------------------------------
def easy():
    a, b = ru(), ru()
    x, y = rv(), rv()

    options = [
        # ∀x (A(x) → ∃y B(y)) → ∀x ∃y (A(x) → B(y))
        Impl(
            Q(x, Impl(Atom(a, x), Q(y, Atom(b, y)))),
            Q(x, Q(y, Impl(Atom(a, x), Atom(b, y))))
        ),
        # ∀x (A(x) → B(x)) → ∀x B(x)   [note: valid only with ∀ on left, but good exercise]
        Impl(
            Q(x, Impl(Atom(a, x), Atom(b, x))),
            Q(x, Atom(b, x))
        ),
        # (∀x A(x) → B(x)) → (∀x A(x) → ∀x B(x))
        Impl(
            Impl(Q(x, Atom(a, x)), Atom(b, x)),
            Impl(Q(x, Atom(a, x)), Q(x, Atom(b, x)))
        ),
        # ∀x (A(x) ∧ B(x)) → ∀x A(x) ∧ ∀x B(x)
        Impl(
            Q(x, And(Atom(a, x), Atom(b, x))),
            And(Q(x, Atom(a, x)), Q(x, Atom(b, x)))
        ),
        # ∀x A(x) ∨ ∀x B(x) → ∀x (A(x) ∨ B(x))
        Impl(
            Or(Q(x, Atom(a, x)), Q(x, Atom(b, x))),
            Q(x, Or(Atom(a, x), Atom(b, x)))
        ),
        # ¬∃x A(x) → ∀x ¬A(x)
        Impl(
            Neg(exists(x, Atom(a, x))),
            forall(x, Neg(Atom(a, x)))
        ),
        # ∀x ¬A(x) → ¬∃x A(x)
        Impl(
            forall(x, Neg(Atom(a, x))),
            Neg(exists(x, Atom(a, x)))
        ),
    ]
    formula = random.choice(options)
    if random.random() < 0.3:
        formula = Neg(formula)
    return formula

# --------------------------------
# Medium formulas
# --------------------------------
def medium():
    F, G = random.sample(PRED_B, 2)
    P, Q_p, R = random.sample(PRED_U, 3)
    x, y, z = rv(), rv(), rv()

    options = [
        # ∀x ∀y (F(x,y) → G(y,x)) ∧ ∀x (P(x) → Q(x)) → ∀x ∀y (F(x,y) → Q(y))
        Impl(
            And(
                Q(x, Q(y, Impl(Atom(F, x, y), Atom(G, y, x)))),
                Q(x, Impl(Atom(P, x), Atom(Q_p, x)))
            ),
            Q(x, Q(y, Impl(Atom(F, x, y), Atom(Q_p, y))))
        ),
        # ∃x ∀y F(x,y) → ∀y ∃x F(x,y)
        Impl(
            exists(x, forall(y, Atom(F, x, y))),
            forall(y, exists(x, Atom(F, x, y)))
        ),
        # ∀x (P(x) → ∀y F(x,y)) ∧ ∀x ∀y (F(x,y) → G(x,y)) → ∀x (P(x) → ∀y G(x,y))
        Impl(
            And(
                forall(x, Impl(Atom(P, x), forall(y, Atom(F, x, y)))),
                forall(x, forall(y, Impl(Atom(F, x, y), Atom(G, x, y))))
            ),
            forall(x, Impl(Atom(P, x), forall(y, Atom(G, x, y))))
        ),
        # ∀x ∀y (F(x,y) ∧ P(x) → G(x,y)) ↔ encoded as two implications
        Impl(
            And(
                Q(x, Q(y, Impl(And(Atom(F, x, y), Atom(P, x)), Atom(G, x, y)))),
                exists(x, Atom(P, x))
            ),
            exists(x, exists(y, Atom(G, x, y)))
        ),
        # ¬∀x P(x) → ∃x ¬P(x)
        Impl(
            Neg(forall(x, Atom(P, x))),
            exists(x, Neg(Atom(P, x)))
        ),
        # ∀x (P(x) ∨ Q(x)) ∧ ∀x (P(x) → R(x)) ∧ ∀x (Q(x) → R(x)) → ∀x R(x)
        Impl(
            And(
                And(
                    forall(x, Or(Atom(P, x), Atom(Q_p, x))),
                    forall(x, Impl(Atom(P, x), Atom(R, x)))
                ),
                forall(x, Impl(Atom(Q_p, x), Atom(R, x)))
            ),
            forall(x, Atom(R, x))
        ),
    ]
    formula = random.choice(options)
    if random.random() < 0.3:
        formula = Neg(formula)
    return formula

# --------------------------------
# Hard formulas
# --------------------------------
def hard():
    F, G, H, K = random.sample(PRED_B, 4)
    P, Q_p, R = random.sample(PRED_U, 3)
    x, y, z, w = rv(), rv(), rv(), rv()

    options = [
        # Transitivity lifting:
        # ∀x∀y∀z (F(x,y) ∧ F(y,z) → F(x,z)) ∧ ∀x∀y (F(x,y) → G(x,y)) ∧ ∀x∀y (G(x,y) → H(x,y))
        # → ∀x∀y∀z (F(x,y) ∧ F(y,z) → H(x,z))
        Impl(
            And(
                And(
                    forall(x, forall(y, forall(z, Impl(And(Atom(F, x, y), Atom(F, y, z)), Atom(F, x, z))))),
                    forall(x, forall(y, Impl(Atom(F, x, y), Atom(G, x, y))))
                ),
                forall(x, forall(y, Impl(Atom(G, x, y), Atom(H, x, y))))
            ),
            forall(x, forall(y, forall(z, Impl(And(Atom(F, x, y), Atom(F, y, z)), Atom(H, x, z)))))
        ),
        # Mixed unary+binary dependency propagation:
        # ∀x (P(x) → ∃y Q(y)) ∧ ∀x∀y (Q(x) ∧ F(x,y) → R(y)) ∧ ∀x∀y (R(x) → G(x,y))
        # → ∀x∀y (P(x) ∧ F(x,y) → G(x,y))
        Impl(
            And(
                And(
                    forall(x, Impl(Atom(P, x), exists(y, Atom(Q_p, y)))),
                    forall(x, forall(y, Impl(And(Atom(Q_p, x), Atom(F, x, y)), Atom(R, y))))
                ),
                forall(x, forall(y, Impl(Atom(R, x), Atom(G, x, y))))
            ),
            forall(x, forall(y, Impl(And(Atom(P, x), Atom(F, x, y)), Atom(G, x, y))))
        ),
        # 4-step relational chain:
        # ∀x∀y (F(x,y) → G(y,x)) ∧ ∀x∀y (G(x,y) → H(x,y)) ∧ ∀x∀y (H(x,y) → K(x,y))
        # → ∀x∀y (F(x,y) → K(y,x))
        Impl(
            And(
                And(
                    forall(x, forall(y, Impl(Atom(F, x, y), Atom(G, y, x)))),
                    forall(x, forall(y, Impl(Atom(G, x, y), Atom(H, x, y))))
                ),
                forall(x, forall(y, Impl(Atom(H, x, y), Atom(K, x, y))))
            ),
            forall(x, forall(y, Impl(Atom(F, x, y), Atom(K, y, x))))
        ),
        # ∀x (P(x) ∨ Q(x)) ∧ ∀x∀y (P(x) ∧ F(x,y) → G(x,y)) ∧ ∀x∀y (Q(x) ∧ F(x,y) → G(x,y))
        # → ∀x∀y (F(x,y) → G(x,y))
        Impl(
            And(
                And(
                    forall(x, Or(Atom(P, x), Atom(Q_p, x))),
                    forall(x, forall(y, Impl(And(Atom(P, x), Atom(F, x, y)), Atom(G, x, y))))
                ),
                forall(x, forall(y, Impl(And(Atom(Q_p, x), Atom(F, x, y)), Atom(G, x, y))))
            ),
            forall(x, forall(y, Impl(Atom(F, x, y), Atom(G, x, y))))
        ),
        # Symmetry + transitivity → universal:
        # ∀x∀y (F(x,y) → F(y,x)) ∧ ∀x∀y∀z (F(x,y) ∧ F(y,z) → F(x,z)) ∧ ∃x∀y F(x,y)
        # → ∀x∀y F(x,y)
        Impl(
            And(
                And(
                    forall(x, forall(y, Impl(Atom(F, x, y), Atom(F, y, x)))),
                    forall(x, forall(y, forall(z, Impl(And(Atom(F, x, y), Atom(F, y, z)), Atom(F, x, z)))))
                ),
                exists(x, forall(y, Atom(F, x, y)))
            ),
            forall(x, forall(y, Atom(F, x, y)))
        ),
    ]
    formula = random.choice(options)
    if random.random() < 0.3:
        formula = Neg(formula)
    return formula

# --------------------------------
# Dataset generator
# --------------------------------
def generate(n=10000):
    data = []
    for i in range(n):
        if i < n // 3:
            data.append(easy())
        elif i < 2 * n // 3:
            data.append(medium())
        else:
            data.append(hard())
    random.shuffle(data)
    return data

# --------------------------------
# Render + deduplicate
# --------------------------------
def deduplicate(formulas):
    seen = set()
    unique = []
    for f in formulas:
        s = render(f)
        if s not in seen:
            seen.add(s)
            unique.append(s)
    return unique

# --------------------------------
# Generate and save
# --------------------------------
qs = generate(1200)
qs = deduplicate(qs)

with open("EQ_fol_diverse.txt", "w") as f:
    for formula in qs:
        f.write(formula + "\n")

print(f"Generated {len(qs)} diverse FOL formulas.")