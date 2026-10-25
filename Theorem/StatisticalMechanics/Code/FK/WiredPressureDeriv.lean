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
import Def.StatisticalMechanics.Code.FK.WiredPressureDeriv
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


theorem wpd_wiredFkZ_logistic (t q : ℝ) :
    wiredFkZ G bdry (fsc_logistic t) q
      = ivp2_Ssum (fun ω => q ^ numClustersWired G bdry ω) (fun ω => (openCount G ω : ℝ)) t
          / (1 + Real.exp t) ^ G.edgeFinset.card := by
  unfold wiredFkZ ivp2_Ssum
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  unfold wiredFkWeight
  rw [ivp2_edgeProduct_logistic G t ω]
  ring


theorem wpd_wiredTiltFreeEnergy_eq_Kcgf (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card)
    (t : ℝ) :
    wpd_wiredTiltFreeEnergy G bdry q t
      = (1 / (G.edgeFinset.card : ℝ))
          * ivp2_Kcgf (fun ω => q ^ numClustersWired G bdry ω)
              (fun ω => (openCount G ω : ℝ)) t := by
  unfold wpd_wiredTiltFreeEnergy ivp2_Kcgf
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hSpos : 0 < ivp2_Ssum w a t := ivp2_Ssum_pos w a hwnn hwpos t
  have hElt : (0:ℝ) < (1 + Real.exp t) ^ G.edgeFinset.card := by positivity
  have hZ : wiredFkZ G bdry (fsc_logistic t) q
      = ivp2_Ssum w a t / (1 + Real.exp t) ^ G.edgeFinset.card := wpd_wiredFkZ_logistic G bdry t q
  rw [hZ, Real.log_div hSpos.ne' hElt.ne', Real.log_pow]
  have hEne : (G.edgeFinset.card : ℝ) ≠ 0 := by exact_mod_cast hE.ne'
  field_simp
  ring


theorem wpd_wiredTiltFreeEnergy_convexOn (q : ℝ) (hq : 0 < q) (hE : 0 < G.edgeFinset.card) :
    ConvexOn ℝ univ (wpd_wiredTiltFreeEnergy G bdry q) := by
  set w : ConfigSpace (Sym2 V) → ℝ := fun ω => q ^ numClustersWired G bdry ω with hw
  set a : ConfigSpace (Sym2 V) → ℝ := fun ω => (openCount G ω : ℝ) with ha
  have hwnn : ∀ ω, 0 ≤ w ω := fun ω => pow_nonneg hq.le _
  have hwpos : ∃ ω, 0 < w ω := ⟨Classical.arbitrary _, pow_pos hq _⟩
  have hconv : ConvexOn ℝ univ (ivp2_Kcgf w a) := ivp2_Kcgf_convexOn w a hwnn hwpos
  have hsmul : ConvexOn ℝ univ (fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t) :=
    hconv.smul (by positivity)
  have heq : wpd_wiredTiltFreeEnergy G bdry q
      = fun t => (1 / (G.edgeFinset.card : ℝ)) * ivp2_Kcgf w a t := by
    funext t; exact wpd_wiredTiltFreeEnergy_eq_Kcgf G bdry q hq hE t
  rw [heq]; exact hsmul


end FK
end StatMech
