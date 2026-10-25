/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/ZagierCyclicPermutationProduct.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Combinatorics.Enumerative.Stirling
import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Algebra.Polynomial.Taylor
import Mathlib.GroupTheory.Perm.Fin
import Def.Combinatorics.Enumerative.Stirling.Part4
import Lemma.Finset.Enumerative.Stirling
import Def.Combinatorics.Enumerative.ZagierCyclicPermutationProduct.Part34
/-!
# Products of two cyclic permutations

This file proves Zagier's formula for the cycle-count distribution of the product of two
cyclic permutations. It also identifies unsigned Stirling numbers of the first kind with
permutations having a prescribed number of cycles, counting fixed points as cycles.
-/


namespace MetaMathlibExt

theorem zagHorizontal_reverseOrder {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) :
    zagHorizontal (zagReverseOrder hn e) = (zagHorizontal e)⁻¹ := by
  let R := zagReverseIndex n hn
  calc
    zagHorizontal (zagReverseOrder hn e) =
        e * (R * finRotate n * R⁻¹) * e⁻¹ := by
      simp only [zagHorizontal, zagReverseOrder, R, mul_inv_rev]
      group
    _ = e * (finRotate n)⁻¹ * e⁻¹ := by
      rw [zagReverseIndex_conj_finRotate]
    _ = (zagHorizontal e)⁻¹ := by
      simp only [zagHorizontal, mul_inv_rev]
      group

theorem zagReverseOrder_basePoint {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n))
    (he : e (zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩) :
    zagReverseOrder hn e (zagBasePoint ⟨0, hn⟩) =
      zagBasePoint ⟨0, hn⟩ := by
  rw [zagReverseOrder, Equiv.Perm.mul_apply, zagReverseIndex_apply]
  have hneg : -(zagBasePoint ⟨0, hn⟩) = zagBasePoint ⟨0, hn⟩ := by
    let hNeZero : NeZero n := ⟨hn.ne'⟩
    apply Fin.ext
    simp [zagBasePoint]
  rw [hneg, he]

theorem zagReverseOrder_symm_apply {n : ℕ} (hn : 0 < n)
    (e : Equiv.Perm (Fin n)) (x : Fin n) :
    (zagReverseOrder hn e).symm x = -(e.symm x) := by
  apply (zagReverseOrder hn e).injective
  rw [Equiv.apply_symm_apply, zagReverseOrder, Equiv.Perm.mul_apply,
    zagReverseIndex_apply, neg_neg, e.apply_symm_apply]

theorem zagReflected_exceedance_iff {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) (x : Fin n) :
    zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹
        (zagHorizontal e x) ↔
      ¬zagExceedance e π x ∧
        π x ≠ e (zagBasePoint x) := by
  rw [zagExceedance, zagReverseOrder_symm_apply,
    zagReflectedVertical_apply_horizontal,
    zagReverseOrder_symm_apply, zagHorizontal_apply_order,
    zagReverseIndex_lt hn]
  constructor
  · rintro ⟨hexc, hzero⟩
    exact ⟨hexc, fun h => hzero (by
      rw [h, e.symm_apply_apply]
      rfl)⟩
  · rintro ⟨hexc, hbase⟩
    refine ⟨hexc, fun hzero => hbase ?_⟩
    apply e.symm.injective
    rw [e.symm_apply_apply]
    exact Fin.ext hzero

theorem zagCard_reflected_exceedances {n : ℕ} (hn : 0 < n)
    (e π : Equiv.Perm (Fin n)) :
    Nat.card {x : Fin n //
        zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ x} =
      n - Nat.card {x : Fin n // zagExceedance e π x} - 1 := by
  classical
  let s := zagHorizontal e
  let base := e (zagBasePoint ⟨0, hn⟩)
  let reflected :
      {x : Fin n // ¬zagExceedance e π x ∧ π x ≠ base} ≃
        {x : Fin n //
          zagExceedance (zagReverseOrder hn e) (zagDiagonal e π)⁻¹ x} :=
    Equiv.subtypeEquiv s (fun x => by
      simpa only [s, base, show zagBasePoint x = zagBasePoint ⟨0, hn⟩ from
        Fin.ext rfl] using (zagReflected_exceedance_iff hn e π x).symm)
  let split :
      {x : Fin n // ¬zagExceedance e π x ∧ π x ≠ base} ≃
        {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 ≠ base} := {
    toFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
    invFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
    left_inv := fun x => rfl
    right_inv := fun x => rfl
  }
  have hspecial : Fintype.card
      {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 = base} = 1 := by
    apply Fintype.card_eq_one_iff.mpr
    let x₀ : Fin n := π.symm base
    have hx₀ : ¬zagExceedance e π x₀ := by
      intro hx
      have hright : e.symm (π x₀) = zagBasePoint ⟨0, hn⟩ := by
        change e.symm (π (π.symm base)) = zagBasePoint ⟨0, hn⟩
        rw [π.apply_symm_apply]
        change e.symm (e (zagBasePoint ⟨0, hn⟩)) = zagBasePoint ⟨0, hn⟩
        rw [e.symm_apply_apply]
      rw [zagExceedance, hright, Fin.lt_def] at hx
      exact Nat.not_lt_zero _ hx
    let q₀ : {x : {x : Fin n // ¬zagExceedance e π x} // π x.1 = base} :=
      ⟨⟨x₀, hx₀⟩, π.apply_symm_apply base⟩
    refine ⟨q₀, fun q => ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply π.injective
    exact q.2.trans q₀.2.symm
  have hanti : Fintype.card {x : Fin n // ¬zagExceedance e π x} =
      n - Fintype.card {x : Fin n // zagExceedance e π x} := by
    simpa only [Fintype.card_fin] using
      Fintype.card_subtype_compl (fun x : Fin n => zagExceedance e π x)
  rw [Nat.card_congr reflected.symm, Nat.card_congr split,
    Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    hspecial, hanti, Nat.card_eq_fintype_card]

theorem zagCycleQuotientCount_inv {n : ℕ}
    (f : Equiv.Perm (Fin n)) :
    cycleQuotientCount f⁻¹ = cycleQuotientCount f := by
  rw [cycleQuotientCount_eq, cycleQuotientCount_eq,
    Equiv.Perm.card_fixedPoints, Equiv.Perm.card_fixedPoints,
    Equiv.Perm.cycleType_inv]

end MetaMathlibExt
