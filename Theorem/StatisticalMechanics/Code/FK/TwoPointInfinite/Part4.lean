/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TwoPointInfinite.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.TwoPoint.Part4
import Theorem.StatisticalMechanics.Code.FK.Limits
import Theorem.StatisticalMechanics.Code.Foundations.MonotoneLimit
import Def.StatisticalMechanics.Code.FK.TwoPointInfinite.Part3
open MeasureTheory Filter Topology SimpleGraph
open scoped BigOperators NNReal Topology

set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice


variable {E : Type*} [Countable E]


theorem isClopen_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsClopen (boxConnEvent d n x y) :=
  IsClopen.preimage ⟨isClosed_discrete _, isOpen_discrete _⟩ (continuous_boxRestrict d n)


theorem measurableSet_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    MeasurableSet (boxConnEvent d n x y) :=
  (isClopen_boxConnEvent d n x y).isOpen.measurableSet


theorem isIncreasing_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    IsIncreasing (boxConnEvent d n x y) :=
  fun _ _ hab ha => connEvent_isIncreasing (boxGraph d n) x y (monotone_boxRestrict d n hab) ha


theorem boxRestrict_extendEdge (d n : ℕ) (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    boxRestrict d n (extendEdge d n ω) = ω := by
  funext eb
  unfold boxRestrict extendEdge
  have hmem : edgeIncl d n eb ∈ Set.range (edgeIncl d n) := ⟨eb, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact edgeIncl_injective d n hmem.choose_spec


theorem extendEdge_preimage_boxConnEvent (d n : ℕ) (x y : boxVerts d n) :
    extendEdge d n ⁻¹' (boxConnEvent d n x y) = connEvent (boxGraph d n) x y := by
  ext ω
  simp only [boxConnEvent, Set.mem_preimage, boxRestrict_extendEdge]


theorem freeFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = twoPointFun (boxGraph d n) p q x y := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hfree : (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((fkPMF (boxGraph d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold freeFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hfree, extendEdge_preimage_boxConnEvent, fkPMF_toMeasure_toReal]
  unfold twoPointFun
  exact Finset.sum_congr rfl fun ω _ => mul_comm _ _


theorem wiredFkProb_pos {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (bdry : V → Prop) [DecidablePred bdry] {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (ω : ConfigSpace (Sym2 V)) :
    0 < wiredFkProb G bdry p q ω :=
  div_pos (wiredFkWeight_pos G bdry hp hp1 hq ω) (wiredFkZ_pos G bdry hp hp1 hq)


theorem wiredFiniteMeasure_real_boxConnEvent (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) (x y : boxVerts d n) :
    (wiredFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real
        (boxConnEvent d n x y)
      = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)),
          (connEvent (boxGraph d n) x y).indicator (fun _ => (1 : ℝ)) ω
            * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
  have hA : MeasurableSet (boxConnEvent d n x y) := measurableSet_boxConnEvent d n x y
  have hw : (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y)
      = ((wiredFkPMF (boxGraph d n) (boxBoundary d n) hp hp1 hq).toMeasure
          (extendEdge d n ⁻¹' (boxConnEvent d n x y))).toReal := by
    unfold wiredFiniteMeasure Measure.real
    simp only [ProbabilityMeasure.coe_mk]
    rw [Measure.map_apply (measurable_extendEdge d n) hA]
  rw [hw, extendEdge_preimage_boxConnEvent, wiredFkPMF_toMeasure_toReal]


theorem freeFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (freeFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (freeFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [freeFiniteMeasure_real_boxConnEvent]
    exact twoPointFun_pos_of_reachable (boxGraph d n) hp hp1 hq h
  rw [← ProbabilityMeasure.coe_apply_eq_real] at hreal
  exact_mod_cast hreal


theorem wiredFiniteMeasure_apply_boxConnEvent_pos (d n : ℕ) {p q : ℝ}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) {x y : boxVerts d n}
    (h : (boxGraph d n).Reachable x y) :
    0 < (wiredFiniteMeasure d n hp hp1 hq) (boxConnEvent d n x y) := by
  have hreal : 0 < (wiredFiniteMeasure d n hp hp1 hq : Measure _).real (boxConnEvent d n x y) := by
    rw [wiredFiniteMeasure_real_boxConnEvent]
    apply Finset.sum_pos'
    · intro ω _
      exact mul_nonneg (Set.indicator_nonneg (fun _ _ => zero_le_one) ω)
        (wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq ω).le
    · refine ⟨fun _ => true, Finset.mem_univ _, ?_⟩
      rw [Set.indicator_of_mem (allOpen_mem_connEvent (boxGraph d n) h), one_mul]
      exact wiredFkProb_pos (boxGraph d n) (boxBoundary d n) hp hp1 hq _
  rw [← ProbabilityMeasure.coe_apply_eq_real] at hreal
  exact_mod_cast hreal


end FK
end StatMech
