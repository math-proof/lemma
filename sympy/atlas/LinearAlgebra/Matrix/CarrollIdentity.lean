/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/CarrollIdentity.lean -/

import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.AffineMonoid.Basic
import Mathlib.LinearAlgebra.Matrix.Adjugate
import Mathlib.Tactic.LinearCombination

namespace MetaMathlibExt.CarrollIdentity

open Matrix

section

variable {m : ℕ} {S : Type*} [CommRing S] (i j : Fin (m + 2))

/-- Row/column splitter for single-deletion minors. -/
private def carrollSplit (p q : Fin (m + 2)) (hp : p = i ∨ p = j) (hq : q = i ∨ q = j)
    (hqp : q ≠ p) :
    Fin (m + 1) → {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 1 :=
  fun a => if h : Fin.succAbove p a = q then Sum.inr 0
    else Sum.inl ⟨Fin.succAbove p a, by
      rcases hp with rfl | rfl <;> rcases hq with rfl | rfl
      · exact absurd rfl hqp
      · exact ⟨Fin.succAbove_ne _ _, h⟩
      · exact ⟨h, Fin.succAbove_ne _ _⟩
      · exact absurd rfl hqp⟩

private lemma carrollSplit_bijective (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
    (hq : q = i ∨ q = j) (hqp : q ≠ p) :
    Function.Bijective (carrollSplit i j p q hp hq hqp) := by
  constructor
  · intro a b hab
    by_cases ha : Fin.succAbove p a = q
    · by_cases hb : Fin.succAbove p b = q
      · exact Fin.succAbove_right_injective (ha.trans hb.symm)
      · simp only [carrollSplit, dif_pos ha, dite_eq_right hb] at hab
        exact absurd hab Sum.inr_ne_inl
    · by_cases hb : Fin.succAbove p b = q
      · simp only [carrollSplit, dite_eq_right ha, dif_pos hb] at hab
        exact absurd hab Sum.inl_ne_inr
      · simp only [carrollSplit, dite_eq_right ha, dite_eq_right hb] at hab
        simp only [Sum.inl.injEq] at hab
        have h2 : Fin.succAbove p a = Fin.succAbove p b :=
          congrArg Subtype.val hab
        exact Fin.succAbove_right_injective h2
  · intro y
    cases y with
    | inl x =>
      have hxp : x.val ≠ p := by
        rcases hp with rfl | rfl
        · exact x.prop.1
        · exact x.prop.2
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hxp
      refine ⟨a, ?_⟩
      have hxq : Fin.succAbove p a ≠ q := by
        rw [ha]
        rcases hq with rfl | rfl
        · exact x.prop.1
        · exact x.prop.2
      simp only [carrollSplit, dite_eq_right hxq]
      exact congrArg Sum.inl (Subtype.ext ha)
    | inr k =>
      obtain ⟨a, ha⟩ := Fin.exists_succAbove_eq hqp
      refine ⟨a, ?_⟩
      simp only [carrollSplit, dif_pos ha]
      exact congrArg Sum.inr (Subsingleton.elim _ _)

private noncomputable def carrollSplitEquiv (p q : Fin (m + 2)) (hp : p = i ∨ p = j)
    (hq : q = i ∨ q = j) (hqp : q ≠ p) : Fin (m + 1) ≃ {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 1 :=
  Equiv.ofBijective _ (carrollSplit_bijective i j p q hp hq hqp)

private def carrollFwd : {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 2 → Fin (m + 2) :=
  Sum.elim Subtype.val ![i, j]

private def carrollBwd :
    Fin (m + 2) → {k : Fin (m + 2) // k ≠ i ∧ k ≠ j} ⊕ Fin 2 :=
  fun k => if h : k ≠ i ∧ k ≠ j then Sum.inl ⟨k, h⟩
    else Sum.inr (if k = i then 0 else 1)

private def carrollFull (hij : i ≠ j) :
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
