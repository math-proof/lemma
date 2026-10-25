/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/CenteredFreeEnergy.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.FKUniqPerEdge.Part3
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Def.StatisticalMechanics.Code.FK.CenteredFreeEnergy.Part3
open scoped BigOperators
open SimpleGraph Filter Topology Set MeasureTheory

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false
set_option linter.style.longLine false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000


namespace StatMech

namespace FK

open StatMech.Lattice


variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]


variable {d : ℕ}


theorem cfe_centered_limit_convexOn (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hconv : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    ConvexOn ℝ univ G :=
  ivp2_convexOn_of_tendsto (l := (atTop : Filter ℕ))
    (fun n => cfe_centered (boxGraph d n) 2) G
    (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hE n))
    hconv


theorem cfe_wiredCentered_tendsto (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (t : ℝ)
    (hfree : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hsv : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ))
      atTop (𝓝 0)) :
    Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 (G t)) := by
  
  have hdiff : ∀ s : ℝ, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 s
        - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s) atTop (𝓝 0) := by
    intro s
    have hbound : ∀ n, |ivp2_tiltFreeEnergy (boxGraph d n) 2 s
          - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 s|
        ≤ ((Finset.univ.filter (boxBoundary d n)).card : ℝ)
            / ((boxGraph d n).edgeFinset.card : ℝ) * Real.log 2 := fun n =>
      wpd_tiltFreeEnergy_sub_le (boxGraph d n) (boxBoundary d n) (by norm_num) (hE n) s
    have hsvlog : Tendsto (fun n =>
        ((Finset.univ.filter (boxBoundary d n)).card : ℝ) / ((boxGraph d n).edgeFinset.card : ℝ)
          * Real.log 2) atTop (𝓝 0) := by
      have := hsv.mul_const (Real.log 2); simpa using this
    refine (tendsto_zero_iff_abs_tendsto_zero _).mpr ?_
    exact squeeze_zero (fun n => abs_nonneg _) hbound hsvlog
  
  have hcdiff : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 0) := by
    have heq : (fun n => cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        = (fun n => (ivp2_tiltFreeEnergy (boxGraph d n) 2 t
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
          - (ivp2_tiltFreeEnergy (boxGraph d n) 2 0
            - wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 0)) := by
      funext n; unfold cfe_centered cfe_wiredCentered; ring
    rw [heq]
    have := (hdiff t).sub (hdiff 0)
    simpa using this
  
  have hwired : Tendsto (fun n => cfe_centered (boxGraph d n) 2 t
        - (cfe_centered (boxGraph d n) 2 t
          - cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)) atTop (𝓝 (G t - 0)) :=
    hfree.sub hcdiff
  simpa using hwired


theorem cfe_genuineFreeIsLeftDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcol : fpe2_GenuineFreeCollapse d N) :
    fpe2_GenuineFreeIsLeftDeriv d N G := by
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcol e' he' s)
  have hbR : ∀ s, freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcol e' he' s)
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hG hbL hbR
    (osc_freeEdgeDensity_left_continuous d N e' t)


theorem cfe_genuineWiredIsRightDeriv (hd : 1 ≤ d) (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    fpe2_GenuineWiredIsRightDeriv d N G := by
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hwiredlim : ∀ t,
      Tendsto (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (G t)) :=
    fun t => cfe_wiredCentered_tendsto hEbox t (hboxfree t) hsv
  intro e' he' t
  have hbL : ∀ s, pressureLeftDeriv G s
      ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s) := by
    intro s
    refine (?_ : pressureLeftDeriv G s
        ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)).trans
      (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos s) (fsc_logistic_lt_one s))
    exact fdd_leftDeriv_le_avgLimit
      (fun n => cfe_centered (boxGraph d n) 2) G
      (fun n => fpd_avgDensity (boxGraph d n))
      (fun n => cfe_centered_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_centered_hasDerivAt (boxGraph d n) (hEbox n) u)
      hboxfree s _ hG (hcolfree e' he' s)
  have hbR : ∀ s, wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic s)
      ≤ pressureRightDeriv G s := by
    intro s
    exact fdd_avgLimit_le_rightDeriv
      (fun n => cfe_wiredCentered (boxGraph d n) (boxBoundary d n) 2) G
      (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2)
      (fun n => cfe_wiredCentered_convexOn (boxGraph d n) (boxBoundary d n) 2 (by norm_num) (hEbox n))
      (fun n u => cfe_wiredCentered_hasDerivAt (boxGraph d n) (boxBoundary d n) (hEbox n) u)
      hwiredlim s _ hG (hcolwired e' he' s)
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hG hbL hbR
    (osc_wiredEdgeDensity_right_continuous d N e' t)


theorem cfe_fk_uniqueness_of_centeredConvergence (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t)))
    (hcolfree : fpe2_GenuineFreeCollapse d N)
    (hcolwired : fpe2_GenuineWiredCollapse d N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  fpe2_fk_uniqueness_of_genuine (lt_of_lt_of_le one_pos hd) N eb heb hG
    (cfe_genuineFreeIsLeftDeriv N hEbox hG hboxfree hcolfree)
    (cfe_genuineWiredIsRightDeriv hd N hEbox hG hboxfree hcolfree hcolwired)


theorem cfe_fk_uniqueness_of_centeredData (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (heb : eb ∈ (boxGraph d N).edgeFinset)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {G : ℝ → ℝ} (hG : ConvexOn ℝ univ G)
    (hboxfree : ∀ t, Tendsto (fun n => cfe_centered (boxGraph d n) 2 t) atTop (𝓝 (G t))) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable :=
  cfe_fk_uniqueness_of_centeredConvergence hd N eb heb hEbox hG hboxfree
    (gec_GenuineFreeCollapse hd N hEbox)
    (gec_GenuineWiredCollapse hd N hEbox)


theorem cfe_centeredConvergence_satisfiable :
    ∃ (gn : ℕ → ℝ → ℝ) (G : ℝ → ℝ),
      (∀ t, Tendsto (fun n => gn n t) atTop (𝓝 (G t))) ∧ G 0 = 0 ∧ ConvexOn ℝ univ G := by
  refine ⟨fun _ _ => 0, fun _ => 0, fun t => tendsto_const_nhds, rfl, ?_⟩
  exact convexOn_const 0 convex_univ


theorem cfe_residue_remark : True := trivial

end FK
end StatMech
