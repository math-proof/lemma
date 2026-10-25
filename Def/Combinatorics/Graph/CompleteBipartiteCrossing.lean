/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Graph/CompleteBipartiteCrossing.lean -/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.Data.Rat.Star
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.RingTheory.Coprime.Lemmas
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Linarith.Lemmas
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify


namespace MetaMathlibExt

/-! # regular drawing crossing count of `K_{n,n}` (Legendre) -/

/-- The point map sending a crossing pair to its interior intersection point. -/
def phi : ((ℕ × ℕ) × (ℕ × ℕ)) → Rat × Rat := fun p => match p with
  | ((i, j), (i', j')) =>
    (((i' : Rat) - (i : Rat)) / (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))),
      (i : Rat) + (((i' : Rat) - (i : Rat)) /
        (((i' : Rat) - (i : Rat)) + ((j : Rat) - (j' : Rat))) * ((j : Rat) - (i : Rat))))

/-- The primitive line data `(a, b, c)` attached to a crossing pair. -/
def key : ((ℕ × ℕ) × (ℕ × ℕ)) → (ℕ × ℕ × ℕ) := fun p => match p with
  | ((i, j), (i', j')) =>
    let d := i' - i; let e := j - j'; let g := Nat.gcd d e
    (d / g, e / g, (e / g) * i + (d / g) * j)

/-- The reconstruction of the intersection point from `(a, b, c)`. -/
def rho : (ℕ × ℕ × ℕ) → Rat × Rat := fun t => match t with
  | (a, b, c) => ((a : Rat) / ((a : Rat) + (b : Rat)), (c : Rat) / ((a : Rat) + (b : Rat)))

/-- The set of crossing pairs, `= C`. -/
def box (n : ℕ) : Finset ((ℕ × ℕ) × (ℕ × ℕ)) :=
  Finset.filter
    (fun p => match p with | ((i, j), (i', j')) => i < i' ∧ j' < j)
    ((Finset.range n ×ˢ Finset.range n) ×ˢ (Finset.range n ×ˢ Finset.range n))

-- start points for direction (a,b): i in [0,n-a), j in [b,n).
def strt (a b n : ℕ) : Finset (ℕ × ℕ) := (Finset.range (n - a)) ×ˢ (Finset.Ico b n)

def predset (a b n : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Ico a (n - a)) ×ˢ (Finset.Ico b (n - b))

def cm (a b : ℕ) : ℕ × ℕ → ℕ := fun q => b * q.1 + a * q.2

def dirs (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range n) ×ˢ (Finset.range n)).filter
    (fun ab => 1 ≤ ab.1 ∧ 1 ≤ ab.2 ∧ Nat.Coprime ab.1 ab.2)

end MetaMathlibExt
