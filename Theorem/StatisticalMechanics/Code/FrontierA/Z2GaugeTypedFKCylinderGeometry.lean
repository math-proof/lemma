/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeTypedFKCylinderGeometry.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinder.Part4
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeTypedFKCylinderGeometry
open scoped BigOperators


namespace StatMech.FrontierA

noncomputable section

theorem sum_fin_pow_natDist_le_two_finiteGeom
    {N : Nat} (r : Real) (hr : 0 <= r) (i : Fin N) :
    (∑ j : Fin N, r ^ Nat.dist i.val j.val) <= 2 * finiteGeom r N := by
  let code : Fin N -> Fin N × Bool := fun j =>
    (⟨Nat.dist i.val j.val, by
      have hi := i.isLt
      have hj := j.isLt
      simp only [Nat.dist]
      omega⟩, decide (i.val <= j.val))
  have hcode : Function.Injective code := by
    intro j₁ j₂ h
    have hdist : Nat.dist i.val j₁.val = Nat.dist i.val j₂.val := by
      exact congrArg (fun q : Fin N × Bool => q.1.val) h
    have hside : (i.val <= j₁.val) ↔ (i.val <= j₂.val) := by
      have hb := congrArg (fun q : Fin N × Bool => q.2) h
      simpa [code] using hb
    apply Fin.ext
    by_cases h₁ : i.val <= j₁.val
    · have h₂ : i.val <= j₂.val := hside.mp h₁
      rw [Nat.dist_eq_sub_of_le h₁, Nat.dist_eq_sub_of_le h₂] at hdist
      omega
    · have h₂ : ¬ i.val <= j₂.val := fun hle => h₁ (hside.mpr hle)
      have hj₁ : j₁.val <= i.val := Nat.le_of_lt (Nat.lt_of_not_ge h₁)
      have hj₂ : j₂.val <= i.val := Nat.le_of_lt (Nat.lt_of_not_ge h₂)
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le hj₁,
        Nat.dist_comm, Nat.dist_eq_sub_of_le hj₂] at hdist
      omega
  calc
    (∑ j : Fin N, r ^ Nat.dist i.val j.val) =
        ∑ q ∈ (Finset.univ : Finset (Fin N)).image code, r ^ q.1.val := by
      rw [Finset.sum_image hcode.injOn]
    _ <= ∑ q : Fin N × Bool, r ^ q.1.val := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact fun _ _ => Finset.mem_univ _
      · intro q _ _
        positivity
    _ = 2 * finiteGeom r N := by
      rw [Fintype.sum_prod_type]
      simp only [Fintype.sum_bool, Finset.sum_add_distrib]
      rw [two_mul]
      congr 1 <;>
        exact Fin.sum_univ_eq_sum_range (fun d => r ^ d) N


theorem finiteGeom_le_inv_one_sub
    {r : Real} (hr0 : 0 <= r) (hr1 : r < 1) (N : Nat) :
    finiteGeom r N <= (1 - r)⁻¹ := by
  have hne : r ≠ 1 := ne_of_lt hr1
  rw [finiteGeom, geom_sum_eq hne]
  have hden : 0 < 1 - r := sub_pos.mpr hr1
  have hrpow : 0 <= r ^ N := pow_nonneg hr0 N
  rw [div_eq_mul_inv]
  have hrewrite : (r ^ N - 1) * (r - 1)⁻¹ =
      (1 - r ^ N) * (1 - r)⁻¹ := by
    rw [show r - 1 = -(1 - r) by ring, inv_neg]
    ring
  rw [hrewrite]
  exact mul_le_of_le_one_left (inv_nonneg.mpr hden.le) (by linarith)


theorem sum_fin_prod_pow_l1_le_four_finiteGeom_sq
    {N : Nat} (r : Real) (hr : 0 <= r) (x y : Fin N) (depth : Nat) :
    (∑ ij : Fin N × Fin N,
        r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)) <=
      4 * (finiteGeom r N) ^ 2 * r ^ depth := by
  have hgeom : 0 <= finiteGeom r N := by
    unfold finiteGeom
    positivity
  have hx := sum_fin_pow_natDist_le_two_finiteGeom r hr x
  have hy := sum_fin_pow_natDist_le_two_finiteGeom r hr y
  have hpow : 0 <= r ^ depth := pow_nonneg hr _
  calc
    (∑ ij : Fin N × Fin N,
        r ^ (Nat.dist x.val ij.1.val + Nat.dist y.val ij.2.val + depth)) =
        ((∑ i : Fin N, r ^ Nat.dist x.val i.val) *
          (∑ j : Fin N, r ^ Nat.dist y.val j.val)) * r ^ depth := by
      rw [Fintype.sum_prod_type]
      simp_rw [pow_add]
      simp_rw [← Finset.sum_mul, ← Finset.mul_sum]
      congr 1
      exact (Finset.sum_mul Finset.univ
        (fun i : Fin N => r ^ Nat.dist x.val i.val)
        (∑ j : Fin N, r ^ Nat.dist y.val j.val)).symm
    _ <= ((2 * finiteGeom r N) * (2 * finiteGeom r N)) * r ^ depth := by
      gcongr
    _ = 4 * (finiteGeom r N) ^ 2 * r ^ depth := by ring


theorem sum_union_le_add_of_nonneg
    {alpha : Type*} [DecidableEq alpha] (s t : Finset alpha)
    (f : alpha -> Real) (hf : forall x, 0 <= f x) :
    ∑ x ∈ s ∪ t, f x <= (∑ x ∈ s, f x) + ∑ x ∈ t, f x := by
  have hinter : 0 <= ∑ x ∈ s ∩ t, f x :=
    Finset.sum_nonneg fun x _ => hf x
  linarith [Finset.sum_union_inter (s₁ := s) (s₂ := t) (f := f)]


theorem nat_mul_pow_le_finiteGeom
    {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) (N : Nat) :
    (N : Real) * r ^ N <= finiteGeom r N := by
  calc
    (N : Real) * r ^ N = ∑ _d ∈ Finset.range N, r ^ N := by simp
    _ <= ∑ d ∈ Finset.range N, r ^ d := by
      apply Finset.sum_le_sum
      intro d hd
      exact pow_le_pow_of_le_one hr0 hr1 (Finset.mem_range.mp hd).le
    _ = finiteGeom r N := rfl


theorem sum_fin_pow_reverseDepth_le_finiteGeom
    {N : Nat} {r : Real} (hr0 : 0 <= r) (hr1 : r <= 1) :
    (∑ z : Fin N, r ^ (N - z.val)) <= finiteGeom r N := by
  let revPerm : Equiv.Perm (Fin N) :=
    Function.Involutive.toPerm Fin.rev (fun z => Fin.rev_rev z)
  calc
    (∑ z : Fin N, r ^ (N - z.val)) <=
        ∑ z : Fin N, r ^ (Fin.rev z).val := by
      apply Finset.sum_le_sum
      intro z _
      apply pow_le_pow_of_le_one hr0 hr1
      simp only [Fin.rev]
      omega
    _ = ∑ z : Fin N, r ^ z.val := by
      simpa [revPerm] using
        (Equiv.sum_comp revPerm (fun z : Fin N => r ^ z.val))
    _ = finiteGeom r N := by
      exact Fin.sum_univ_eq_sum_range (fun d => r ^ d) N


end
end StatMech.FrontierA
