/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/FKUniqPerEdge.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.EdgeMarginal.Part2
import Theorem.StatisticalMechanics.Code.FK.FiniteEnergy.Part4
import Theorem.StatisticalMechanics.Code.FK.DensityBounds
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredDomChain.Part4
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessDensity
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessSkeleton.Part3
import Theorem.StatisticalMechanics.Code.FK.RotationInvariance.Part3
import Theorem.StatisticalMechanics.Code.FK.UniformBulkDeviation.Part2
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
import Theorem.StatisticalMechanics.Code.FK.BoxFeketePerVolume.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniqPrimitives
import Def.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part2
open Set Filter Topology
open scoped BigOperators
open StatMech.FK

set_option linter.unusedSectionVars false
set_option linter.style.longLine false
set_option linter.unusedDecidableInType false


namespace StatMech

namespace FK

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


open StatMech.Lattice

variable {d : ℕ}


theorem fpe2_genuineFreeIsLeftDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N g := by
  intro e' he' t
  
  have hbL : ∀ s, pressureLeftDeriv g s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcol e' he' s)
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv g s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcol e' he' s)
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hg hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)


theorem fpe2_genuineWiredIsRightDeriv (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N g := by
  
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hwiredlim : ∀ t,
      Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (g t)) :=
    fun t => wpd_wiredTiltFreeEnergy_tendsto 2 (by norm_num) hEbox g t (hboxfree t) hsv
  intro e' he' t
  
  have hbL : ∀ s, pressureLeftDeriv g s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv g s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) u)
      hboxfree s _ hg (hcolfree e' he' s)
  
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv g s := by
    intro s
    exact wpd_wiredAvgDensity_le_rightDeriv 2 (by norm_num) hEbox g hg hwiredlim s _
      (hcolwired e' he' s)
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hg hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)


theorem fpe2_fk_uniqueness_of_boxFekete (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hg
    (fpe2_genuineFreeIsLeftDeriv N hEbox hg hboxfree hcolfree)
    (fpe2_genuineWiredIsRightDeriv hd N hEbox hg hboxfree hcolfree hcolwired)


theorem fpe2_fk_uniqueness_of_perVolume (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (hdata : ∀ t, bpv_PerVolumeFreeEnergyData d t)
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  obtain ⟨G, hboxfree, hG⟩ := bpv_exists_convex_ivPressure_of_perVolume hEbox hdata
  exact fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (fpe2_genuineFreeIsLeftDeriv N hEbox hG hboxfree hcolfree)
    (fpe2_genuineWiredIsRightDeriv hd N hEbox hG hboxfree hcolfree hcolwired)


theorem fpe2_genuineFreeCollapse_of_all (N : ℕ)
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
    fpe2_GenuineFreeCollapse d N :=
  fun e' _ t => hcol e' t


theorem fpe2_genuineWiredCollapse_of_all (N : ℕ)
    (hcol : wpd_AvgWiredDensityCollapse (d := d) N) :
    fpe2_GenuineWiredCollapse d N :=
  fun e' _ t => hcol e' t


theorem fpe2_genuineFree_target_const (hd : 0 < d) (N : ℕ)
    {e₁ e₂ : Sym2 (boxVerts d N)} (h1 : e₁ ∈ (boxGraph d N).edgeFinset)
    (h2 : e₂ ∈ (boxGraph d N).edgeFinset) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e₁) (fsc_logistic t)
      = freeEdgeDensity d 2 (edgeIncl d N e₂) (fsc_logistic t) := by
  rw [rot_free_box_edge_const hd N e₁ h1 (fsc_logistic_pos t) (fsc_logistic_lt_one t),
    rot_free_box_edge_const hd N e₂ h2 (fsc_logistic_pos t) (fsc_logistic_lt_one t)]

end FK
end StatMech
