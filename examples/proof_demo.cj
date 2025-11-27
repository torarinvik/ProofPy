# =============================================================================
# ProofPy Proof Features Demo
# =============================================================================
# This file demonstrates the new Lean 4-style proof features in CertiJSON:
# - Inductive propositions (class ... in prop)
# - Universal quantification (forall)
# - Theorems with proofs
# - Fin (bounded naturals) from stdlib

import Std.Nat
import Std.Bool
import Std.Fin
import Std.Decidable

# =============================================================================
# INDUCTIVE PROPOSITIONS
# =============================================================================

# MyTrue is a proposition with a trivial proof
class MyTrue in prop:
    MyTrue.intro

# MyFalse is a proposition with no constructors (unprovable)
class MyFalse in prop:
    pass

# =============================================================================
# SIMPLE DEFINITIONS
# =============================================================================

def is_zero(n: Nat) -> Bool:
    match n:
        case zero:
            return True
        case succ(m):
            return False

def pred(n: Nat) -> Nat:
    match n:
        case zero:
            return zero
        case succ(m):
            return m

# =============================================================================
# THEOREMS
# =============================================================================

# A trivial theorem: we can always produce MyTrue
theorem always_true:
    forall n: Nat, MyTrue
proof:
    return \n -> MyTrue.intro

# =============================================================================
# USING FIN (BOUNDED NATURALS) FROM STDLIB
# =============================================================================

# Safe array indexing: Fin n guarantees 0 <= i < n
def safe_get_val(n: Nat, i: Fin(n)) -> Nat:
    return Fin.val(n, i)

# Create Fin values with proofs
def get_zero_fin(n: Nat) -> Fin(succ(n)):
    return Fin.zero(n)

# =============================================================================
# DECIDABILITY
# =============================================================================

# Check if value is in bounds
def check_bounds(n: Nat, i: Nat) -> Bool:
    # In real code, this would be: Dec(Lt i n)
    match n:
        case zero:
            return False
        case succ(m):
            match i:
                case zero:
                    return True
                case succ(j):
                    return check_bounds(m, j)

# =============================================================================
# MAIN
# =============================================================================

def main() -> Nat:
    # Get a Fin value for safe indexing
    idx: Fin(succ(succ(succ(zero)))) = Fin.zero(succ(succ(zero)))
    return Fin.val(succ(succ(succ(zero))), idx)
