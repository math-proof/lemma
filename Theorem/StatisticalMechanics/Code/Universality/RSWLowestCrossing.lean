/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/RSWLowestCrossing.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
import Theorem.StatisticalMechanics.Code.Percolation.OffClusterIndep.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SurfaceReassembly
import Theorem.StatisticalMechanics.Code.RSW.Defs.Part7
import Theorem.StatisticalMechanics.Code.Inequalities.Harris
import Theorem.StatisticalMechanics.Code.Lattice.JordanExteriorClosure.Part8
import Theorem.StatisticalMechanics.Code.Lattice.ClosedContourSeparation.Part2
import Theorem.StatisticalMechanics.Code.Lattice.StraightWalk.Part4
import Theorem.StatisticalMechanics.Code.Universality.CrossingTranslationInvariance.Part3
import Theorem.StatisticalMechanics.Code.Universality.ConnectedRCoastClose.Part13
import Mathlib.Combinatorics.SimpleGraph.Walk.Counting
import Def.StatisticalMechanics.Code.Universality.RSWLowestCrossing
open Function MeasureTheory Set
open scoped ENNReal NNReal BigOperators


namespace StatMech

namespace Universality

open StatMech.Percolation

open StatMech.Lattice

open StatMech.RSW.Box

variable {E : Type*}


theorem rlc_cornerReturn_support_inside {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n) {p : Site 2}
    (hp : p ∈ (rlc_cornerReturn x z).support)
    (hpR : p ∈ rect 0 (2 * n) (-n) n) :
    p = (z : Site 2) ∨ p = (x : Site 2) := by
  have hz0 : (z : Site 2) 0 = 2 * n := z.2.2
  have hx1 : (x : Site 2) 1 = n := x.2.2
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  simp only [rlc_cornerReturn, SimpleGraph.Walk.mem_support_append_iff,
    SimpleGraph.Walk.support_copy, SimpleGraph.Walk.support_reverse] at hp
  rcases hp with hp | hp | hp | hp
  · obtain ⟨hp1, hp0lo, hp0hi⟩ :=
      jec_hsegRight_support ((z : Site 2) 1) (2 * n) 1 hp
    rw [mem_rect] at hpR
    by_cases heq : p 0 = 2 * n
    · left
      funext i
      fin_cases i
      · simpa [hz0] using heq
      · simpa using hp1
    · omega
  · obtain ⟨hp0, _hp1lo, _hp1hi⟩ :=
      jec_vsegUp_support (2 * n + 1) ((z : Site 2) 1)
        (n + 1 - (z : Site 2) 1).toNat hp
    rw [mem_rect] at hpR
    omega
  · obtain ⟨hp1, _hp0lo, _hp0hi⟩ :=
      jec_hsegRight_support (n + 1) ((x : Site 2) 0)
        (2 * n + 1 - (x : Site 2) 0).toNat (by simpa using hp)
    rw [mem_rect] at hpR
    omega
  · obtain ⟨hp0, hp1lo, hp1hi⟩ :=
      jec_vsegUp_support ((x : Site 2) 0) n 1 (by simpa using hp)
    rw [mem_rect] at hpR
    right
    funext i
    fin_cases i
    · simpa using hp0
    · have hp1 : p 1 = n := by omega
      simpa [hx1] using hp1


theorem rlc_cornerReturn_rayCount_zero {n : ℤ}
    (x : topSide 0 (2 * n) (-n) n)
    (z : rightSide 0 (2 * n) (-n) n)
    (p : Site 2) (hpR : p ∈ rect 0 (2 * n) (-n) n) :
    jec_rayCount p (rlc_cornerReturn x z) = 0 := by
  have hz1le : (z : Site 2) 1 ≤ n := by
    have hzSide := z.2
    rw [mem_rightSide, mem_rect] at hzSide
    exact hzSide.1.2.2.2
  have hx0le : (x : Site 2) 0 ≤ 2 * n := by
    have hxSide := x.2
    rw [mem_topSide, mem_rect] at hxSide
    exact hxSide.1.2.1
  rw [mem_rect] at hpR
  simp only [rlc_cornerReturn, jec_rayCount_append, jec_rayCount_copy,
    jec_rayCount_reverse, jec_rayCount_hsegRight, jec_rayCount_vsegUp]
  split_ifs <;> omega


theorem rlc_ray_eq_below_right_of_avoids {n : ℤ}
    (t : rightSide 0 (2 * n) (-n) n) {a b : Site 2}
    (w : (hypercubicLattice 2).Walk a b)
    (hbox : ∀ p ∈ w.support, p ∈ rect 0 (2 * n) (-n) n)
    (havoid : (t : Site 2) ∉ w.support) :
    jec_rayCount (t : Site 2) w =
      crossCount (jec_belowSet ((t : Site 2) 1)) w := by
  classical
  rw [jec_rayCount, crossCount]
  refine List.countP_congr ?_
  intro e he
  obtain ⟨u, v⟩ := e
  have hadj : (hypercubicLattice 2).Adj u v := w.adj_of_mem_edges he
  have huSupp : u ∈ w.support := w.fst_mem_support_of_mem_edges he
  have hvSupp : v ∈ w.support := w.snd_mem_support_of_mem_edges he
  have huR := hbox u huSupp
  have hvR := hbox v hvSupp
  have ht0 : (t : Site 2) 0 = 2 * n := t.2.2
  simp only [decide_eq_true_eq]
  show jec_rayEdge (t : Site 2) s(u, v) ↔
    bdEdge (jec_belowSet ((t : Site 2) 1)) s(u, v)
  rw [jec_rayEdge_mk,
    jec_belowSet_bdEdge ((t : Site 2) 1) u v hadj]
  constructor
  · rintro ⟨⟨hcol, _hle⟩, hrow⟩
    exact ⟨hcol, hrow⟩
  · rintro ⟨hcol, hrow⟩
    refine ⟨⟨hcol, ?_⟩, hrow⟩
    rw [mem_rect] at huR hvR
    by_contra hle
    have hcolEq : u 0 = 2 * n := by omega
    rcases hrow with hrow | hrow
    · have hvEq : v = (t : Site 2) := by
        funext i
        fin_cases i
        · have hv0 : v 0 = 2 * n := by omega
          exact hv0.trans ht0.symm
        · exact hrow.2
      exact havoid (hvEq ▸ hvSupp)
    · have huEq : u = (t : Site 2) := by
        funext i
        fin_cases i
        · exact hcolEq.trans ht0.symm
        · exact hrow.2
      exact havoid (huEq ▸ huSupp)


theorem rlc_harris_cylinder {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) {A B : Set (ConfigSpace E)}
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B)
    (T U : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B
      ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) := by
  classical
  let F := T ∪ U
  have hAF : DependsOn (A.indicator (fun _ => (1 : ℝ))) (F : Set E) :=
    hA.mono (by simp [F])
  have hBF : DependsOn (B.indicator (fun _ => (1 : ℝ))) (F : Set E) :=
    hB.mono (by simp [F])
  have hcylA : A = cylinder F (F.restrict '' A) :=
    eq_cylinder_restrict_image A F hAF
  have hcylB : B = cylinder F (F.restrict '' B) :=
    eq_cylinder_restrict_image B F hBF
  have hPA : (bernoulliProductMeasure (E := E) p hp).real A =
      (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' A) := by
    conv_lhs => rw [hcylA]
    rw [realProb_cylinder]
  have hPB : (bernoulliProductMeasure (E := E) p hp).real B =
      (bernoulliProductMeasure (E := ↥F) p hp).real (F.restrict '' B) := by
    conv_lhs => rw [hcylB]
    rw [realProb_cylinder]
  have hPAB : (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) =
      (bernoulliProductMeasure (E := ↥F) p hp).real
        ((F.restrict '' A) ∩ (F.restrict '' B)) := by
    conv_lhs => rw [hcylA, hcylB, inter_cylinder_same]
    rw [realProb_cylinder]
  rw [hPA, hPB, hPAB]
  exact harris_inequality hp
    (isIncreasing_restrict_image A hAinc F)
    (isIncreasing_restrict_image B hBinc F)


theorem rlc_harris_three_cylinder {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) {A B C : Set (ConfigSpace E)}
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) (hCinc : IsIncreasing C)
    (T U V : Finset E)
    (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
    (hC : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E)) :
    (bernoulliProductMeasure (E := E) p hp).real A
        * (bernoulliProductMeasure (E := E) p hp).real B
        * (bernoulliProductMeasure (E := E) p hp).real C
      ≤ (bernoulliProductMeasure (E := E) p hp).real (A ∩ B ∩ C) := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hAB : μ.real A * μ.real B ≤ μ.real (A ∩ B) :=
    rlc_harris_cylinder p hp hAinc hBinc T U hA hB
  have hABdep : DependsOn ((A ∩ B).indicator (fun _ => (1 : ℝ)))
      ((T ∪ U : Finset E) : Set E) := by
    simpa only [Finset.coe_union] using dependsOn_inter hA hB
  have hABC : μ.real (A ∩ B) * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    rlc_harris_cylinder p hp (hAinc.inter hBinc) hCinc (T ∪ U) V hABdep hC
  calc
    μ.real A * μ.real B * μ.real C
        ≤ μ.real (A ∩ B) * μ.real C :=
          mul_le_mul_of_nonneg_right hAB measureReal_nonneg
    _ ≤ μ.real (A ∩ B ∩ C) := hABC


theorem rlc_diagonal_event_lower_bound {E : Type*} [Countable E] [DecidableEq E]
    (p : ℝ≥0) (hp : p ≤ 1) (α : ℝ) (hα : 0 ≤ α)
    (A B C Diag : Set (ConfigSpace E))
    (T U V : Finset E)
    (hAinc : IsIncreasing A) (hBinc : IsIncreasing B) (hCinc : IsIncreasing C)
    (hAdep : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
    (hBdep : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E))
    (hCdep : DependsOn (C.indicator (fun _ => (1 : ℝ))) (V : Set E))
    (hAprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real A)
    (hBprob : α / 2 ≤ (bernoulliProductMeasure (E := E) p hp).real B)
    (hCprob : α ≤ (bernoulliProductMeasure (E := E) p hp).real C)
    (hforce : A ∩ B ∩ C ⊆ Diag) :
    α ^ 3 / 4 ≤ (bernoulliProductMeasure (E := E) p hp).real Diag := by
  let μ := bernoulliProductMeasure (E := E) p hp
  have hfkg : μ.real A * μ.real B * μ.real C ≤ μ.real (A ∩ B ∩ C) :=
    rlc_harris_three_cylinder p hp hAinc hBinc hCinc T U V hAdep hBdep hCdep
  have hlower : (α / 2) * (α / 2) * α ≤ μ.real A * μ.real B * μ.real C := by
    have hAB : (α / 2) * (α / 2) ≤ μ.real A * μ.real B := by
      exact mul_le_mul hAprob hBprob (by positivity) measureReal_nonneg
    exact mul_le_mul hAB hCprob hα
      (mul_nonneg measureReal_nonneg measureReal_nonneg)
  calc
    α ^ 3 / 4 = (α / 2) * (α / 2) * α := by ring
    _ ≤ μ.real A * μ.real B * μ.real C := hlower
    _ ≤ μ.real (A ∩ B ∩ C) := hfkg
    _ ≤ μ.real Diag := measureReal_mono hforce


theorem rlc_connector_half_of_dual_reflection {E : Type*}
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (sigma : ConfigSpace E → ConfigSpace E)
    (hsigma : MeasurePreserving sigma mu mu)
    (Connect : Set (ConfigSpace E)) (hConnect : MeasurableSet Connect)
    (hdual : Connectᶜ ⊆ sigma ⁻¹' Connect) :
    (1 : ℝ) / 2 ≤ mu.real Connect := by
  have hmono : mu.real Connectᶜ ≤ mu.real (sigma ⁻¹' Connect) :=
    measureReal_mono hdual
  have hpres : mu.real (sigma ⁻¹' Connect) = mu.real Connect :=
    hsigma.measureReal_preimage hConnect.nullMeasurableSet
  have hcompl : mu.real Connectᶜ = 1 - mu.real Connect := by
    rw [measureReal_compl hConnect, probReal_univ]
  rw [hpres, hcompl] at hmono
  linarith


theorem rlc_connector_half_of_dual_comparison {E : Type*}
    (mu : Measure (ConfigSpace E)) [IsProbabilityMeasure mu]
    (sigma : ConfigSpace E → ConfigSpace E)
    (hsigma : MeasurePreserving sigma mu mu)
    (Connect DualConnect : Set (ConfigSpace E))
    (hConnect : MeasurableSet Connect)
    (hDualConnect : MeasurableSet DualConnect)
    (hdual : Connectᶜ ⊆ sigma ⁻¹' DualConnect)
    (hcompare : mu.real DualConnect ≤ mu.real Connect) :
    (1 : ℝ) / 2 ≤ mu.real Connect := by
  have hmono : mu.real Connectᶜ ≤
      mu.real (sigma ⁻¹' DualConnect) :=
    measureReal_mono hdual
  have hpres : mu.real (sigma ⁻¹' DualConnect) =
      mu.real DualConnect :=
    hsigma.measureReal_preimage hDualConnect.nullMeasurableSet
  have hcompl : mu.real Connectᶜ = 1 - mu.real Connect := by
    rw [measureReal_compl hConnect, probReal_univ]
  rw [hpres, hcompl] at hmono
  linarith


end Universality
end StatMech
