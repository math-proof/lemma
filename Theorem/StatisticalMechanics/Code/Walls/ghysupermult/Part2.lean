/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/ghysupermult.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Def.StatisticalMechanics.Code.Walls.ghysupermult
open Finset BigOperators
open Classical

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option maxHeartbeats 1600000


namespace StatMech.Walls

open StatMech StatMech.Ising StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


lemma ghy_zeta_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (S : Finset (Sym2 V)) : 0 ≤ ghy_zeta E J hf S := by
  unfold ghy_zeta
  apply mul_nonneg
  · exact div_nonneg (ZJ_pos _ _ _).le (ZJ_pos _ _ _).le
  · exact Finset.prod_nonneg (fun e _ => (Real.cosh_pos _).le)


lemma ghy_tanh_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ Real.tanh t := by
  rw [Real.tanh_eq_sinh_div_cosh]
  exact div_nonneg (Real.sinh_nonneg_iff.mpr ht) (Real.cosh_pos _).le


lemma ghy_rho_nonneg (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (S : Finset (Sym2 V)) : 0 ≤ ghy_rho E J hf S := by
  unfold ghy_rho
  exact mul_nonneg (ghy_zeta_nonneg E J hf S)
    (Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e)))


lemma ghy_zeta_supermult (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hdisj : Disjoint S₁ S₂) :
    ghy_zeta E J hf S₁ * ghy_zeta E J hf S₂ ≤ ghy_zeta E J hf (S₁ ∪ S₂) := by
  unfold ghy_zeta
  rw [Finset.prod_union hdisj]
  set Z := ZJ E J hf with hZdef
  set a := ZJ (E \ S₁) J hf with hadef
  set b := ZJ (E \ S₂) J hf with hbdef
  set d := ZJ (E \ (S₁ ∪ S₂)) J hf with hddef
  set P₁ := ∏ e ∈ S₁, Real.cosh (J e) with hP1def
  set P₂ := ∏ e ∈ S₂, Real.cosh (J e) with hP2def
  have hZ : 0 < Z := ZJ_pos E J hf
  have hZne : Z ≠ 0 := ne_of_gt hZ
  have hP1 : 0 < P₁ := Finset.prod_pos (fun e _ => Real.cosh_pos _)
  have hP2 : 0 < P₂ := Finset.prod_pos (fun e _ => Real.cosh_pos _)
  have hdep : a * b ≤ Z * d := ghy_Zdep_supermod E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj
  
  have key : a * b / (Z * Z) ≤ d / Z := by
    rw [div_le_div_iff₀ (by positivity) hZ]
    nlinarith [hdep, hZ, mul_pos hZ hZ]
  have hL : a / Z * P₁ * (b / Z * P₂) = a * b / (Z * Z) * (P₁ * P₂) := by
    field_simp
  rw [hL]
  exact mul_le_mul_of_nonneg_right key (by positivity)


lemma ghy_rho_supermult (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hdisj : Disjoint S₁ S₂) :
    ghy_rho E J hf S₁ * ghy_rho E J hf S₂ ≤ ghy_rho E J hf (S₁ ∪ S₂) := by
  unfold ghy_rho
  rw [Finset.prod_union hdisj]
  have hzeta := ghy_zeta_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ hdisj
  have hT1 : 0 ≤ ∏ e ∈ S₁, Real.tanh (J e) :=
    Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e))
  have hT2 : 0 ≤ ∏ e ∈ S₂, Real.tanh (J e) :=
    Finset.prod_nonneg (fun e _ => ghy_tanh_nonneg (hJ e))
  have hstep := mul_le_mul_of_nonneg_right hzeta (mul_nonneg hT1 hT2)
  calc ghy_zeta E J hf S₁ * (∏ e ∈ S₁, Real.tanh (J e))
          * (ghy_zeta E J hf S₂ * (∏ e ∈ S₂, Real.tanh (J e)))
      = ghy_zeta E J hf S₁ * ghy_zeta E J hf S₂
          * ((∏ e ∈ S₁, Real.tanh (J e)) * (∏ e ∈ S₂, Real.tanh (J e))) := by ring
    _ ≤ ghy_zeta E J hf (S₁ ∪ S₂)
          * ((∏ e ∈ S₁, Real.tanh (J e)) * (∏ e ∈ S₂, Real.tanh (J e))) := hstep


theorem ghy_rho_supermult_three (E : Finset (Sym2 V)) (J : Sym2 V → ℝ) (hf : V → ℝ)
    (hJ : ∀ e, 0 ≤ J e) (hhf : ∀ v, 0 ≤ hf v) (hndE : ∀ e ∈ E, ¬ e.IsDiag)
    (S₁ S₂ S₃ : Finset (Sym2 V)) (hS₁ : S₁ ⊆ E) (hS₂ : S₂ ⊆ E) (hS₃ : S₃ ⊆ E)
    (h12 : Disjoint S₁ S₂) (h13 : Disjoint S₁ S₃) (h23 : Disjoint S₂ S₃) :
    ghy_rho E J hf S₁ * ghy_rho E J hf S₂ * ghy_rho E J hf S₃
      ≤ ghy_rho E J hf (S₁ ∪ S₂ ∪ S₃) := by
  have hStep1 := ghy_rho_supermult E J hf hJ hhf hndE S₁ S₂ hS₁ hS₂ h12
  have hUnion12 : S₁ ∪ S₂ ⊆ E := Finset.union_subset hS₁ hS₂
  have hDisj123 : Disjoint (S₁ ∪ S₂) S₃ := Finset.disjoint_union_left.mpr ⟨h13, h23⟩
  have hStep2 := ghy_rho_supermult E J hf hJ hhf hndE (S₁ ∪ S₂) S₃ hUnion12 hS₃ hDisj123
  have hρ3 : 0 ≤ ghy_rho E J hf S₃ := ghy_rho_nonneg E J hf hJ S₃
  calc ghy_rho E J hf S₁ * ghy_rho E J hf S₂ * ghy_rho E J hf S₃
      ≤ ghy_rho E J hf (S₁ ∪ S₂) * ghy_rho E J hf S₃ :=
        mul_le_mul_of_nonneg_right hStep1 hρ3
    _ ≤ ghy_rho E J hf (S₁ ∪ S₂ ∪ S₃) := hStep2

end StatMech.Walls
