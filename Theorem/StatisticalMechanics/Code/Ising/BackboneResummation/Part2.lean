/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneResummation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.RandomCurrent.Part10
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
import Theorem.StatisticalMechanics.Code.Ising.TwoReplicaWeighted.Part2
import Theorem.StatisticalMechanics.Code.Ising.AizenmanSignDominance.Part2
import Theorem.StatisticalMechanics.Code.Ising.HdomNativeWeight.Part3
import Def.StatisticalMechanics.Code.Ising.BackboneResummation.Part2
open Finset Classical
open scoped symmDiff BigOperators

set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem bbr_surgery_satisfiable (β : ℝ) (J : Sym2 V → ℝ) (M : Finset (Current V)) (A : Finset V)
    (o x y : V) (hno : bbr_allFilter G M o x y = ∅) :
    bbr_BackboneSurgery G β J M A o x y := by
  refine ⟨id, ?_, ?_, ?_⟩ <;> rw [hno] <;> intro m hm <;> simp at hm


theorem bbr_hdom_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (A : Finset V) (o x y : V)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A)
      ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A := by
  obtain ⟨Ψ, hΨmem, hΨinj, hbound⟩ := hsurg
  have hgnn : ∀ b ∈ bbr_noneFilter G M o x y, 0 ≤ hnw_mass G β J b A := by
    intro b _; exact bbr_mass_nonneg G β J hβ hJ b A
  have := bbr_inj_domination (bbr_allFilter G M o x y) (bbr_noneFilter G M o x y)
    (fun m => hnw_mass G β J m A) (fun m => hnw_mass G β J m A) Ψ hΨmem hΨinj hgnn hbound
  simpa only [bbr_allFilter, bbr_noneFilter] using this


theorem bbr_closure_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    0 ≤ ∑ m ∈ M, hnw_gap G β J m A o x y :=
  hnw_closure_of_hdom G β J M hnd A hm hox hoy hxy hcoh
    (bbr_hdom_of_surgery G β J hβ hJ M A o x y hsurg)


theorem bbr_ghs_of_surgery (β : ℝ) (J : Sym2 V → ℝ) (hβ : 0 ≤ β) (hJ : ∀ e, 0 ≤ J e)
    (M : Finset (Current V)) (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag) (A : Finset V)
    (hm : ∀ m ∈ M, Sharpness.sources G m = A)
    {o x y : V} (hox : o ≠ x) (hoy : o ≠ y) (hxy : x ≠ y)
    (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
    (hsurg : bbr_BackboneSurgery G β J M A o x y) :
    (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}))
      + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}))
      ≤ ∑ m ∈ M, hnw_mass G β J m A :=
  hnw_ghs_distinct_site_of_hdom G β J M hnd A hm hox hoy hxy hcoh
    (bbr_hdom_of_surgery G β J hβ hJ M A o x y hsurg)

end Ising
end StatMech
