/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.ODE.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Set.Piecewise
import Mathlib.Topology.Sequences
open Filter Function Metric Set
open scoped NNReal Topology

/-!
# Maximal solutions of ordinary differential equations

This file proves global existence for continuous vector fields that are globally Lipschitz in the
state variable, and constructs maximal solutions for locally Lipschitz vector fields on open
subsets of spacetime.  The latter solutions eventually leave every compact subset at each finite
or infinite end of their interval of definition.
-/


/-- Solutions that agree on the overlap of two open domains glue to a solution on their union. -/
theorem hasDerivAt_piecewise_union_of_eqOn
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {v : ℝ → E → E} {x y : ℝ → E} {I J : Set ℝ}
    (hI : IsOpen I) (hJ : IsOpen J)
    (hx : ∀ t ∈ I, HasDerivAt x (v t (x t)) t)
    (hy : ∀ t ∈ J, HasDerivAt y (v t (y t)) t)
    (hxy : EqOn x y (I ∩ J)) :
    ∃ z : ℝ → E, EqOn z x I ∧ EqOn z y J ∧
      ∀ t ∈ I ∪ J, HasDerivAt z (v t (z t)) t := by
  classical
  refine ⟨I.piecewise x y, Set.piecewise_eqOn I x y, ?_, ?_⟩
  · intro t ht
    by_cases htI : t ∈ I
    · simp [Set.piecewise, htI, hxy ⟨htI, ht⟩]
    · simp [Set.piecewise, htI]
  intro t ht
  by_cases htI : t ∈ I
  · have heq : I.piecewise x y =ᶠ[𝓝 t] x := by
      filter_upwards [hI.mem_nhds htI] with u hu
      simp [Set.piecewise, hu]
    simpa [Set.piecewise, htI] using (hx t htI).congr_of_eventuallyEq heq
  · have htJ : t ∈ J := ht.resolve_left htI
    have heq : I.piecewise x y =ᶠ[𝓝 t] y := by
      filter_upwards [hJ.mem_nhds htJ] with u hu
      by_cases huI : u ∈ I
      · simp [Set.piecewise, huI, hxy ⟨huI, hu⟩]
      · simp [Set.piecewise, huI]
    simpa [Set.piecewise, htI] using (hy t htJ).congr_of_eventuallyEq heq

namespace ODE.MaximalSolutionWanted

lemma odeMaximalLocalFlow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {U : Set (ℝ × E)} {f : ℝ × E → E} (hU : IsOpen U) (hf : ContinuousOn f U)
    (hlip : ∀ p ∈ U, ∃ C : NNReal, ∃ s ∈ nhds p,
      ∀ t : ℝ, ∀ x y : E, (t, x) ∈ s ∩ U → (t, y) ∈ s ∩ U →
        dist (f (t, x)) (f (t, y)) ≤ C * dist x y)
    {p : ℝ × E} (hp : p ∈ U) :
    ∃ W ∈ nhds p, ∃ ε > 0, ∀ q ∈ W, ∃ x : ℝ → E, x q.1 = q.2 ∧
      ∀ t ∈ Ioo (q.1 - ε) (q.1 + ε),
        (t, x t) ∈ U ∧ HasDerivAt x (f (t, x t)) t := by
  classical
  obtain ⟨C, s, hs, hC⟩ := hlip p hp
  have hfp : ContinuousAt f p := hf.continuousAt (hU.mem_nhds hp)
  have hnorm : {q | ‖f q‖ < ‖f p‖ + 1} ∈ nhds p :=
    hfp.norm (Iio_mem_nhds (lt_add_one ‖f p‖))
  have hw : (s ∩ U) ∩ {q | ‖f q‖ < ‖f p‖ + 1} ∈ nhds p :=
    inter_mem (inter_mem hs (hU.mem_nhds hp)) hnorm
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hw
  let B : ℝ := ‖f p‖ + 1
  have hB : 0 < B := by
    dsimp [B]
    exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
  let ε : ℝ := min (δ / 8) (δ / (8 * B))
  have hε : 0 < ε := by simp [ε, hδ, hB]
  refine ⟨ball p (δ / 8), ball_mem_nhds p (by positivity), ε, hε, ?_⟩
  intro q hq
  have hqt : dist q.1 p.1 < δ / 8 := by
    calc
      dist q.1 p.1 ≤ dist q p := by simp [Prod.dist_eq]
      _ < δ / 8 := hq
  have hqx : dist q.2 p.2 < δ / 8 := by
    calc
      dist q.2 p.2 ≤ dist q p := by simp [Prod.dist_eq]
      _ < δ / 8 := hq
  let a : NNReal := ⟨δ / 2, by positivity⟩
  let r : NNReal := ⟨δ / 4, by positivity⟩
  let L : NNReal := ⟨B, hB.le⟩
  have hbox (t : ℝ) (ht : t ∈ Icc (q.1 - ε) (q.1 + ε))
      (y : E) (hy : y ∈ closedBall p.2 a) : (t, y) ∈ (s ∩ U) ∩ {z | ‖f z‖ < B} := by
    apply hball
    rw [mem_ball, Prod.dist_eq, max_lt_iff]
    constructor
    · calc
        dist t p.1 ≤ dist t q.1 + dist q.1 p.1 := dist_triangle _ _ _
        _ < ε + δ / 8 := by
          apply add_lt_add_of_le_of_lt _ hqt
          rw [Real.dist_eq]
          refine (abs_le (G := ℝ) (a := t - q.1) (b := ε)).2 ⟨?_, ?_⟩
          · linarith [ht.1]
          · linarith [ht.2]
        _ ≤ δ / 4 := by dsimp [ε]; linarith [min_le_left (δ / 8) (δ / (8 * B))]
        _ < δ := by linarith
    · calc
        dist y p.2 ≤ δ / 2 := by
          change dist y p.2 ≤ δ / 2 at hy
          exact hy
        _ < δ := by linarith
  have hqball : q.2 ∈ closedBall p.2 r := by
    change dist q.2 p.2 ≤ δ / 4
    exact hqx.le.trans (by linarith)
  have hqtime : q.1 ∈ Icc (q.1 - ε) (q.1 + ε) := by simp [hε.le]
  let q₀ : Icc (q.1 - ε) (q.1 + ε) := ⟨q.1, hqtime⟩
  have hPL : IsPicardLindelof (fun t y ↦ f (t, y)) q₀ p.2 a r L C := by
    refine IsPicardLindelof.mk ?_ ?_ ?_ ?_
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro x hx y hy
      exact hC t x y (hbox t ht x hx).1 (hbox t ht y hy).1
    · intro y hy
      exact hf.comp (continuous_id.prodMk continuous_const).continuousOn
        (fun t ht ↦ (hbox t ht y hy).1.2)
    · intro t ht y hy
      exact le_of_lt (hbox t ht y hy).2
    · change B * max ((q.1 + ε) - q.1) (q.1 - (q.1 - ε)) ≤ δ / 2 - δ / 4
      rw [add_sub_cancel_left, sub_sub_cancel, max_self]
      have he : ε ≤ δ / (8 * B) := min_le_right _ _
      have : B * ε ≤ δ / 8 := by
        calc
          B * ε ≤ B * (δ / (8 * B)) := by gcongr
          _ = δ / 8 := by field_simp
      linarith
  obtain ⟨α, hα⟩ := ODE.FunSpace.exists_isFixedPt_next hPL hqball
  refine ⟨α.compProj, ?_, fun t ht ↦ ⟨?_, ?_⟩⟩
  · change α.compProj (q₀ : ℝ) = q.2
    rw [ODE.FunSpace.compProj_val, ← hα, ODE.FunSpace.next_apply₀]
  · exact (hbox t (Ioo_subset_Icc_self ht) _
      (α.compProj_mem_closedBall hPL.mul_max_le)).1.2
  · apply HasDerivWithinAt.hasDerivAt ?_ (Icc_mem_nhds ht.1 ht.2)
    apply (ODE.hasDerivWithinAt_picard_Icc q₀.2 hPL.continuousOn_uncurry
      α.continuous_compProj.continuousOn
      (fun _ _ ↦ α.compProj_mem_closedBall hPL.mul_max_le) q.2
      (Ioo_subset_Icc_self ht)).congr_of_mem _ (Ioo_subset_Icc_self ht)
    intro t' ht'
    nth_rw 1 [← hα]
    rw [ODE.FunSpace.compProj_of_mem ht', ODE.FunSpace.next_apply]

end ODE.MaximalSolutionWanted
