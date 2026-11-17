/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Baranyai.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.Fin
public import Mathlib.Algebra.GroupWithZero.Divisibility
public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Card
public import Mathlib.Combinatorics.Hall.Basic
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators

@[expose] public section

namespace MetaMathlibExt

section

/-- Count of positions `(i, j)` with `A i j = S`. -/
def baranyai_cnt {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = S)).card

/-- The strengthened induction hypothesis: `L` partial classes over `U`. -/
def baranyai_Good (n k L a : ℕ) (U : Finset (Fin n))
    (A : Fin L → Fin a → Finset (Fin n)) : Prop :=
  (∀ i j, A i j ⊆ U) ∧
  (∀ i j j', j ≠ j' → Disjoint (A i j) (A i j')) ∧
  (∀ i, Finset.univ.biUnion (A i) = U) ∧
  (∀ i j, (A i j).card ≤ k) ∧
  (∀ S ⊆ U, S.card ≤ k → baranyai_cnt A S = (n - U.card).choose (k - S.card))

/-- Insert `x` into the chosen block of each class. -/
def baranyai_extend {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (J : Fin L → Fin a) (x : Fin n) : Fin L → Fin a → Finset (Fin n) :=
  fun i j => if j = J i then insert x (A i j) else A i j

end
end MetaMathlibExt
