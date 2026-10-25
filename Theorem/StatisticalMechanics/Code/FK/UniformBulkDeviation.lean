/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/UniformBulkDeviation.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.FK.SpatialCollapse
import Theorem.StatisticalMechanics.Code.FK.OneSidedContinuity
import Theorem.StatisticalMechanics.Code.FK.WiredPressureDeriv.Part4
import Theorem.StatisticalMechanics.Code.FK.FKDensityDeriv.Part2
import Theorem.StatisticalMechanics.Code.FK.FKUniquenessClose3
import Theorem.StatisticalMechanics.Code.FK.FKLimitsClose.Part3
import Def.StatisticalMechanics.Code.FK.UniformBulkDeviation
open MeasureTheory Set Filter Topology Real
open scoped BigOperators

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.openClassical false
set_option linter.style.setOption false


namespace StatMech

namespace FK

open ConfigSpace StatMech.Lattice

variable {d : ℕ}


theorem ubd_freeDensity_le_rightDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ≤ pressureRightDeriv g t :=
  fdd_avgLimit_le_rightDeriv
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
    (fun n => fpd_avgDensity (boxGraph d n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) s)
    hboxfree t _ hg (hcol e' t)


theorem ubd_leftDeriv_le_freeDensity (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
  fdd_leftDeriv_le_avgLimit
    (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2) g
    (fun n => fpd_avgDensity (boxGraph d n))
    (fun n => ivp2_tiltFreeEnergy_convexOn (boxGraph d n) 2 (by norm_num) (hEbox n))
    (fun n s => fpd_tiltFreeEnergy_deriv_eq_avgDensity (boxGraph d n) (hEbox n) s)
    hboxfree t _ hg (hcol e' t)


theorem ubd_freeDensityIsLeftDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N) :
    fdd_FreeDensityIsLeftDeriv (d := d) N g := by
  intro e' t
  exact fdd_eq_leftDeriv_of_bracket_leftContinuous hg
    (fun s => ubd_leftDeriv_le_freeDensity N hEbox g hg hboxfree hcol e' s)
    (fun s => ubd_freeDensity_le_rightDeriv N hEbox g hg hboxfree hcol e' s)
    (osc_freeEdgeDensity_left_continuous d N e' t)


theorem ubd_leftDeriv_le_wiredDensity (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N)
    (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    pressureLeftDeriv g t ≤ wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) :=
  (ubd_leftDeriv_le_freeDensity N hEbox g hg hboxfree hcol e' t).trans
    (freeEdgeDensity_q2_le_wiredEdgeDensity d N e' (fsc_logistic_pos t) (fsc_logistic_lt_one t))


theorem ubd_wiredDensityIsRightDeriv (N : ℕ)
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (g : ℝ → ℝ) (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcol : ubd_FreeGrowingBoxCollapse (d := d) N)
    (hub : fdd_WiredDensityUpperBound (d := d) N g) :
    fdd_WiredDensityIsRightDeriv (d := d) N g := by
  intro e' t
  exact fdd_eq_rightDeriv_of_bracket_rightContinuous hg
    (fun s => ubd_leftDeriv_le_wiredDensity N hEbox g hg hboxfree hcol e' s)
    (fun s => hub e' s)
    (osc_wiredEdgeDensity_right_continuous d N e' t)


theorem ubd_fk_uniqueness_of_growingBoxCollapse (hd : 1 ≤ d) (N : ℕ) (eb : Sym2 (boxVerts d N))
    (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    {g : ℝ → ℝ} (hg : ConvexOn ℝ univ g)
    (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
    (hcolfree : ubd_FreeGrowingBoxCollapse (d := d) N)
    (hcolwired : wpd_AvgWiredDensityCollapse (d := d) N) :
    {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧
        eventMassProb (fuc_freeMass d N t) A
          ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
  
  have hsv := fup_surfaceVolume_tendsto_zero d hd
  have hwiredlim : ∀ t,
      Tendsto (fun n => wpd_wiredTiltFreeEnergy (boxGraph d n) (boxBoundary d n) 2 t)
        atTop (𝓝 (g t)) :=
    fun t => wpd_wiredTiltFreeEnergy_tendsto 2 (by norm_num) hEbox g t (hboxfree t) hsv
  
  have hub : fdd_WiredDensityUpperBound (d := d) N g :=
    wpd_wiredDensityUpperBound N hEbox g hg hwiredlim hcolwired
  
  have hfree : fdd_FreeDensityIsLeftDeriv (d := d) N g :=
    ubd_freeDensityIsLeftDeriv N hEbox g hg hboxfree hcolfree
  have hwired : fdd_WiredDensityIsRightDeriv (d := d) N g :=
    ubd_wiredDensityIsRightDeriv N hEbox g hg hboxfree hcolfree hub
  exact fdd_fk_uniqueness N eb hg hwired hfree


theorem ubd_freeEdgeDensity_mem_Icc (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    freeEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hlim := dfi_free_density_eq_limit N e' hp hp1
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_nonneg (boxGraph d (N + k)) hp hp1 (by norm_num) _)
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      adc_edgeMargProb_fkProb_le_one (boxGraph d (N + k)) hp hp1 (by norm_num) _)


theorem ubd_edgeMargProb_wiredFkProb_nonneg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (e : Sym2 V) :
    0 ≤ edgeMargProb (wiredFkProb G bdry p q) e := by
  unfold edgeMargProb
  apply Finset.sum_nonneg
  intro ω _
  apply mul_nonneg _ (wiredFkProb_nonneg G bdry hp hp1 hq ω)
  split <;> norm_num


theorem ubd_edgeMargProb_wiredFkProb_le_one {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry]
    {p q : ℝ} (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (e : Sym2 V) :
    edgeMargProb (wiredFkProb G bdry p q) e ≤ 1 := by
  unfold edgeMargProb
  calc ∑ ω : ConfigSpace (Sym2 V), (if ω e then (1:ℝ) else 0) * wiredFkProb G bdry p q ω
      ≤ ∑ ω : ConfigSpace (Sym2 V), wiredFkProb G bdry p q ω := by
        apply Finset.sum_le_sum
        intro ω _
        have hb : (if ω e then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
        calc (if ω e then (1:ℝ) else 0) * wiredFkProb G bdry p q ω
            ≤ 1 * wiredFkProb G bdry p q ω :=
              mul_le_mul_of_nonneg_right hb (wiredFkProb_nonneg G bdry hp hp1 hq ω)
          _ = wiredFkProb G bdry p q ω := one_mul _
    _ = 1 := wiredFkProb_sum_eq_one G bdry hp hp1 hq


theorem ubd_wiredEdgeDensity_mem_Icc (N : ℕ) (e' : Sym2 (boxVerts d N)) (t : ℝ) :
    wiredEdgeDensity d 2 (edgeIncl d N e') (fsc_logistic t) ∈ Set.Icc (0:ℝ) 1 := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hlim := dfi_wired_density_eq_limit N e' hp hp1
  constructor
  · exact ge_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (by norm_num) _)
  · exact le_of_tendsto hlim (Filter.Eventually.of_forall fun k =>
      ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d (N + k)) (boxBoundary d (N + k))
        hp hp1 (by norm_num) _)


theorem ubd_avgWiredDensity_eq_sum (n : ℕ) (t : ℝ) :
    wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t
      = (1 / ((boxGraph d n).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d n).edgeFinset,
              edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e :=
  wpd_avgWiredDensity_eq_sum_edgeMarg (boxGraph d n) (boxBoundary d n) 2 t


theorem ubd_growingBox_wiredCollapse (t : ℝ)
    (hE : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
    (L : ℝ) (hL0 : 0 ≤ L) (hL1 : L ≤ 1)
    (In : (n : ℕ) → Finset (Sym2 (boxVerts d n)))
    (hIE : ∀ n, In n ⊆ (boxGraph d n).edgeFinset)
    (δ : ℕ → ℝ) (hδ0 : ∀ n, 0 ≤ δ n) (hδlim : Tendsto δ atTop (𝓝 0))
    (hin : ∀ n, ∀ e ∈ In n,
      |edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e - L| ≤ δ n)
    (hbdy : Tendsto (fun n =>
        (((boxGraph d n).edgeFinset.card - (In n).card : ℝ)) / (boxGraph d n).edgeFinset.card)
      atTop (𝓝 0)) :
    Tendsto (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t) atTop (𝓝 L) := by
  have hp := fsc_logistic_pos t
  have hp1 := fsc_logistic_lt_one t
  have hrepr : (fun n => wpd_avgWiredDensity (boxGraph d n) (boxBoundary d n) 2 t)
      = fun n => (1 / ((boxGraph d n).edgeFinset.card : ℝ))
          * ∑ e ∈ (boxGraph d n).edgeFinset,
              edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e := by
    funext n; exact ubd_avgWiredDensity_eq_sum n t
  rw [hrepr]
  exact adc_absavg_tendsto
    (ι := fun n => Sym2 (boxVerts d n))
    (En := fun n => (boxGraph d n).edgeFinset) In
    (fn := fun n e => edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) (fsc_logistic t) 2) e)
    L δ hIE
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_nonneg (boxGraph d n) (boxBoundary d n)
      hp hp1 (by norm_num) e)
    (fun n e _ => ubd_edgeMargProb_wiredFkProb_le_one (boxGraph d n) (boxBoundary d n)
      hp hp1 (by norm_num) e)
    hL0 hL1 hδ0 hδlim hin hE hbdy


end FK
end StatMech
