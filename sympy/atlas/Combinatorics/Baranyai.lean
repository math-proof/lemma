/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Baranyai.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Fintype.Fin
import Mathlib.Algebra.GroupWithZero.Divisibility
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Combinatorics.Hall.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

namespace MetaMathlibExt

section

/-- Count of positions `(i, j)` with `A i j = S`. -/
private def baranyai_cnt {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (S : Finset (Fin n)) : ℕ :=
  (Finset.univ.filter (fun p : Fin L × Fin a => A p.1 p.2 = S)).card

/-- The strengthened induction hypothesis: `L` partial classes over `U`. -/
private def baranyai_Good (n k L a : ℕ) (U : Finset (Fin n))
    (A : Fin L → Fin a → Finset (Fin n)) : Prop :=
  (∀ i j, A i j ⊆ U) ∧
  (∀ i j j', j ≠ j' → Disjoint (A i j) (A i j')) ∧
  (∀ i, Finset.univ.biUnion (A i) = U) ∧
  (∀ i j, (A i j).card ≤ k) ∧
  (∀ S ⊆ U, S.card ≤ k → baranyai_cnt A S = (n - U.card).choose (k - S.card))

/-- Insert `x` into the chosen block of each class. -/
private def baranyai_extend {n L a : ℕ} (A : Fin L → Fin a → Finset (Fin n))
    (J : Fin L → Fin a) (x : Fin n) : Fin L → Fin a → Finset (Fin n) :=
  fun i j => if j = J i then insert x (A i j) else A i j
end
end MetaMathlibExt
