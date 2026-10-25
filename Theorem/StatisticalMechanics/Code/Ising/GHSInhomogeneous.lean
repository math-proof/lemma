/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GHSInhomogeneous.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.GHSInhomVertexPartition.Part3
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeSum
import Theorem.StatisticalMechanics.Code.Sharpness.GHSConcavity
open scoped BigOperators symmDiff
open Finset SimpleGraph Set

set_option maxHeartbeats 2400000


namespace StatMech.Ising

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


section Relabel

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

theorem ghsi_fieldSum_relabel (sigma : V ≃ W) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (omega : ConfigSpace W) :
    (∑ x : V, hfV x * spin (isingCfgEquiv sigma omega) x) =
      ∑ y : W, hfW y * spin omega y := by
  have hcomp : (fun x : V => hfV x * spin (isingCfgEquiv sigma omega) x) =
      fun x => hfW (sigma x) * spin omega (sigma x) := by
    funext x
    rw [hhf]
    rfl
  rw [hcomp]
  exact Equiv.sum_comp sigma (fun y : W => hfW y * spin omega y)

theorem ghsi_wJ_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (omega : ConfigSpace W) :
    wJ G.edgeFinset (fun _ => beta) hfV (isingCfgEquiv sigma omega) =
      wJ H.edgeFinset (fun _ => beta) hfW omega := by
  unfold wJ
  congr 1
  rw [show (∑ e ∈ G.edgeFinset, beta * bond (isingCfgEquiv sigma omega) e) =
      beta * ∑ e ∈ G.edgeFinset, bond (isingCfgEquiv sigma omega) e by
    rw [Finset.mul_sum]]
  rw [show (∑ e ∈ H.edgeFinset, beta * bond omega e) =
      beta * ∑ e ∈ H.edgeFinset, bond omega e by rw [Finset.mul_sum]]
  rw [sum_bond_isingCfgEquiv G H sigma hsigma omega,
    ghsi_fieldSum_relabel sigma hfV hfW hhf omega]

theorem ghsi_ZJ_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) :
    ZJ G.edgeFinset (fun _ => beta) hfV =
      ZJ H.edgeFinset (fun _ => beta) hfW := by
  unfold ZJ
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => wJ G.edgeFinset (fun _ => beta) hfV omega)]
  exact Finset.sum_congr rfl
    (fun omega _ => ghsi_wJ_const_relabel G H sigma hsigma beta hfV hfW hhf omega)

theorem ghsi_expJ_spin_const_relabel (sigma : V ≃ W)
    (hsigma : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
    (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (hhf : ∀ x, hfV x = hfW (sigma x)) (x : V) :
    expJ G.edgeFinset (fun _ => beta) hfV (fun omega => spin omega x) =
      expJ H.edgeFinset (fun _ => beta) hfW (fun omega => spin omega (sigma x)) := by
  unfold expJ
  rw [ghsi_ZJ_const_relabel G H sigma hsigma beta hfV hfW hhf]
  rw [← Equiv.sum_comp (isingCfgEquiv sigma)
    (fun omega => spin omega x * wJ G.edgeFinset (fun _ => beta) hfV omega)]
  apply congrArg (fun z => z / ZJ H.edgeFinset (fun _ => beta) hfW)
  apply Finset.sum_congr rfl
  intro omega _
  rw [spin_isingCfgEquiv,
    ghsi_wJ_const_relabel G H sigma hsigma beta hfV hfW hhf]

end Relabel


section Sum

variable {W : Type*} [Fintype W] [DecidableEq W]

variable (H : SimpleGraph W) [DecidableRel H.Adj]

theorem ghsi_wJ_sum (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (s : ConfigSpace V) (t : ConfigSpace W) :
    wJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW)
        (isingSumConfigEquiv.symm (s, t)) =
      wJ G.edgeFinset (fun _ => beta) hfV s *
        wJ H.edgeFinset (fun _ => beta) hfW t := by
  unfold wJ
  rw [← Real.exp_add]
  congr 1
  rw [show (∑ e ∈ (G ⊕g H).edgeFinset,
      beta * bond (isingSumConfigEquiv.symm (s, t)) e) =
      beta * ∑ e ∈ (G ⊕g H).edgeFinset,
        bond (isingSumConfigEquiv.symm (s, t)) e by rw [Finset.mul_sum]]
  rw [sum_bond_isingSumConfigEquiv_symm G H s t]
  rw [show (∑ e ∈ G.edgeFinset, beta * bond s e) =
      beta * ∑ e ∈ G.edgeFinset, bond s e by rw [Finset.mul_sum]]
  rw [show (∑ e ∈ H.edgeFinset, beta * bond t e) =
      beta * ∑ e ∈ H.edgeFinset, bond t e by rw [Finset.mul_sum]]
  rw [Fintype.sum_sum_type]
  simp only [spin_isingSumConfigEquiv_symm_inl,
    spin_isingSumConfigEquiv_symm_inr, Sum.elim_inl, Sum.elim_inr]
  ring

theorem ghsi_ZJ_sum (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ) :
    ZJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW) =
      ZJ G.edgeFinset (fun _ => beta) hfV *
        ZJ H.edgeFinset (fun _ => beta) hfW := by
  unfold ZJ
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsi_wJ_sum G H beta hfV hfW]
  simp_rw [← Finset.mul_sum]
  rw [← Finset.sum_mul]

theorem ghsi_expJ_spin_sum_inl (beta : ℝ) (hfV : V → ℝ) (hfW : W → ℝ)
    (x : V) :
    expJ (G ⊕g H).edgeFinset (fun _ => beta) (Sum.elim hfV hfW)
        (fun s => spin s (Sum.inl x)) =
      expJ G.edgeFinset (fun _ => beta) hfV (fun s => spin s x) := by
  unfold expJ
  rw [ghsi_ZJ_sum G H]
  rw [← Equiv.sum_comp isingSumConfigEquiv.symm]
  rw [Fintype.sum_prod_type]
  simp_rw [ghsi_wJ_sum G H beta hfV hfW,
    spin_isingSumConfigEquiv_symm_inl]
  have hW : ZJ H.edgeFinset (fun _ => beta) hfW ≠ 0 := (ZJ_pos _ _ _).ne'
  have hnum : (∑ s : ConfigSpace V, ∑ t : ConfigSpace W,
      spin s x * (wJ G.edgeFinset (fun _ => beta) hfV s *
        wJ H.edgeFinset (fun _ => beta) hfW t)) =
      (∑ s : ConfigSpace V, spin s x * wJ G.edgeFinset (fun _ => beta) hfV s) *
        ZJ H.edgeFinset (fun _ => beta) hfW := by
    unfold ZJ
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro s _
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hnum]
  field_simp

end Sum
end StatMech.Ising
