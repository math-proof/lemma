/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.VonNeumannAlgebra.Basic
import Mathlib.Topology.Algebra.Module.Spaces.PointwiseConvergenceCLM
import Mathlib.Analysis.LocallyConvex.PointwiseConvergence
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.LocallyConvex.WithSeminorms
import Mathlib.Analysis.Normed.Module.HahnBanach
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2
import Mathlib.Analysis.CStarAlgebra.ContinuousLinearMap
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Instances
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Isometric
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Range
import Def.Analysis.CStarAlgebra.KaplanskyDensity.Part3
open scoped PointwiseConvergenceCLM
open Topology


namespace Analysis.CStarAlgebra.KaplanskyDensityWanted

universe u

section KapClosure

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Membership in `kapSotClosure` unfolds definitionally. -/
theorem kapMem_sotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H))
    (T : H →L[ℂ] H) :
    T ∈ kapSotClosure S ↔
      kapOfBounded T ∈ closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} :=
  Iff.rfl

/-- The SOT-closure is norm-closed. -/
theorem kapIsClosed_sotClosure (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    IsClosed (↑(kapSotClosure S) : Set (H →L[ℂ] H)) := by
  have heq : (↑(kapSotClosure S) : Set (H →L[ℂ] H))
      = kapOfBounded ⁻¹' (closure {p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S}) := by
    ext T
    exact Iff.rfl
  rw [heq]
  exact IsClosed.preimage kapOfBounded_continuous isClosed_closure

end KapClosure

section KapScale

variable {H : Type u} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Norm-closure points of `S` in the unit ball lie in the SOT-closure of the ball. -/
theorem kapOfBounded_mem_closure_ball (S : StarSubalgebra ℂ (H →L[ℂ] H))
    {T : H →L[ℂ] H} (hT : T ∈ S.topologicalClosure) (hnorm : ‖T‖ ≤ 1) :
    kapOfBounded T ∈ closure ({p : H →Lₚₜ[ℂ] H | toBounded p ∈ ↑S} ∩
      {p : H →Lₚₜ[ℂ] H | ‖toBounded p‖ ≤ 1}) := by
  have hTmem : T ∈ (S.topologicalClosure : Set (H →L[ℂ] H)) := hT
  rw [StarSubalgebra.topologicalClosure_coe] at hTmem
  obtain ⟨s, hsS, hsLim⟩ := mem_closure_iff_seq_limit.mp hTmem
  set c : ℕ → ℝ := fun n => max 1 ‖s n‖ with hcdef
  have hc1 : ∀ n, 1 ≤ c n := fun n => le_max_left _ _
  have hcnorm : ∀ n, ‖s n‖ ≤ c n := fun n => le_max_right _ _
  have hcpos : ∀ n, (0 : ℝ) < c n := fun n => lt_of_lt_of_le zero_lt_one (hc1 n)
  have hclim : Filter.Tendsto c Filter.atTop (𝓝 1) := by
    have h1 : Filter.Tendsto (fun n => ‖s n‖) Filter.atTop (𝓝 ‖T‖) :=
      hsLim.norm
    have h2 := (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop)).max h1
    rwa [max_eq_left hnorm] at h2
  set t : ℕ → H →L[ℂ] H := fun n => ((((c n)⁻¹ : ℝ) : ℂ)) • s n with htdef
  have htS : ∀ n, t n ∈ (↑S : Set (H →L[ℂ] H)) := fun n => S.smul_mem (hsS n) _
  have htnorm : ∀ n, ‖t n‖ ≤ 1 := by
    intro n
    have hpos : (0 : ℝ) ≤ (c n)⁻¹ := le_of_lt (inv_pos.mpr (hcpos n))
    calc ‖t n‖ = (c n)⁻¹ * ‖s n‖ := by
          rw [htdef]
          simp only [norm_smul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg hpos]
      _ ≤ (c n)⁻¹ * c n := by
          exact mul_le_mul_of_nonneg_left (hcnorm n) hpos
      _ = 1 := inv_mul_cancel₀ (ne_of_gt (hcpos n))
  have hinv : Filter.Tendsto (fun n => (c n)⁻¹) Filter.atTop (𝓝 1) := by
    have h := hclim.inv₀ (by norm_num : (1 : ℝ) ≠ 0)
    simpa using h
  have hscal : Filter.Tendsto (fun n => ((((c n)⁻¹ : ℝ) : ℂ))) Filter.atTop (𝓝 1) := by
    have hcast := (Complex.continuous_ofReal.tendsto (1 : ℝ)).comp hinv
    simp only [Complex.ofReal_one] at hcast
    exact hcast
  have htlim : Filter.Tendsto t Filter.atTop (𝓝 T) := by
    have h := hscal.smul hsLim
    simpa [htdef, one_smul] using h
  have hsot : Filter.Tendsto (fun n => kapOfBounded (t n)) Filter.atTop
      (𝓝 (kapOfBounded T)) :=
    (kapOfBounded_continuous.tendsto _).comp htlim
  apply mem_closure_of_tendsto hsot
  filter_upwards with n
  constructor
  · change toBounded (kapOfBounded (t n)) ∈ ↑S
    rw [kapToBounded_ofBounded]
    exact htS n
  · change ‖toBounded (kapOfBounded (t n))‖ ≤ 1
    rw [kapToBounded_ofBounded]
    exact htnorm n

end KapScale
end Analysis.CStarAlgebra.KaplanskyDensityWanted
