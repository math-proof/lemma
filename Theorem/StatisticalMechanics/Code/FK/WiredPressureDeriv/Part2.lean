/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredPressureDeriv.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.BoxSecantData
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Def.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part2
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]

variable (bdry : V → Prop) [DecidablePred bdry]


theorem wpd_wiredCgfMean_eq_openCount_expect (q : ℝ) (hq : 0 < q) (t : ℝ) :
    wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))
      = ivp2_S1 (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t
          / ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω)
              (fun ω => (openCount G ω : ℝ)) t := by
  have hSpos : (0:ℝ) < ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω)
      (fun ω => (openCount G ω : ℝ)) t :=
    ivp2_Ssum_pos _ _ (fun ω => pow_nonneg hq.le _) ⟨Classical.arbitrary _, pow_pos hq _⟩ t
  unfold ivp2_Ssum at hSpos
  have hEpos : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  unfold wpd_wiredFkExpect ivp2_S1 ivp2_Ssum wiredFkProb wiredFkWeight
  rw [wpd_wiredFkZ_logistic G bdry t q, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [ivp2_edgeProduct_logistic G t ω]
  unfold ivp2_Ssum
  simp only []
  rw [eq_div_iff hSpos.ne']
  field_simp


theorem wpd_wiredTiltFreeEnergy_hasDerivAt (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    HasDerivAt (wpd_wiredTiltFreeEnergy G bdry q)
      ((1 / (G.edgeFinset.card : ℝ))
        * wpd_wiredFkExpect G bdry (fsc_logistic t) q (fun ω => (openCount G ω : ℝ))) t := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have heq : wpd_wiredTiltFreeEnergy G bdry q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext s; exact wpd_wiredTiltFreeEnergy_eq_Kcgf G bdry q hq hE s
  rw [heq, wpd_wiredCgfMean_eq_openCount_expect G bdry q hq t]
  exact (ivp2_Kcgf_hasDerivAt w a hwnn hwpos t).const_mul _


end FK
end StatMech
