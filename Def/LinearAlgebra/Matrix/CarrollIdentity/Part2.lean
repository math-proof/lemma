/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination
import Theorem.LinearAlgebra.Matrix.CarrollIdentity


namespace MetaMathlibExt.CarrollIdentity

open Matrix

section

variable {m : ℕ} {S : Type*} [CommRing S] (i j : Fin (m + 2))

noncomputable def carrollSplitEquiv (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
    (hq : q = i ∨ q = j) (hqp : q ≠ p) : Fin (m + 1) ≃ {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 1 :=
  Equiv.ofBijective _ (carrollSplit_bijective i j p q hp hq hqp)

def carrollFwd : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 2 → Fin (m + 2) :=
  Sum.elim Subtype.val ![i, j]

def carrollBwd :
    Fin (m + 2) → {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 2 :=
  fun k => if h : k ≠ i ∧ k ≠ j then Sum.inl ⟨k, h⟩
    else Sum.inr (if k = i then 0 else 1)

def carrollFull (hij : i ≠ j) :
    {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 2 ≃ Fin (m + 2) :=
  Equiv.mk (carrollFwd i j) (carrollBwd i j) (by
    intro x
    cases x with
    | inl x =>
      have e : carrollFwd i j (Sum.inl x) = x.val := rfl
      rw [e]
      simp only [carrollBwd, dif_pos x.prop]
    | inr k =>
      fin_cases k <;> simp [carrollFwd, carrollBwd, hij, Ne.symm hij]) (by
    intro k
    by_cases h : k ≠ i ∧ k ≠ j
    · have e : carrollBwd i j k = Sum.inl ⟨k, h⟩ := by
        simp only [carrollBwd, dif_pos h]
      have e2 : carrollFwd i j (Sum.inl ⟨k, h⟩) = k := rfl
      rw [e, e2]
    · have e : carrollBwd i j k =
        Sum.inr (if k = i then (0 : Fin 2) else 1) := by
        simp only [carrollBwd, dite_eq_right h]
      rw [e]
      by_cases hki : k = i
      · simp only [ite_eq_left hki, carrollFwd, Sum.elim_inr, Matrix.cons_val_zero]
        exact hki.symm
      · have hkj : k = j := by
          have hB : ¬ k ≠ j := fun hj => h ⟨hki, hj⟩
          exact not_not.mp hB
        simp only [ite_eq_right hki, carrollFwd, Sum.elim_inr, Matrix.cons_val_one,
          Matrix.cons_val_zero]
        exact hkj.symm)

end
end MetaMathlibExt.CarrollIdentity
