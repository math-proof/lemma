-- Author: @toskua, Avocado
-- Provenance: Adam Kiezun authored the original formalization
-- (commit 8a13ba393c1d23f85b900081c600941a4bdd56dc); @toskua, Avocado
-- authored only the Convexity.StdSimplex representation migration.

import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Exposed
import Mathlib.Analysis.Convex.Segment
import Mathlib.Analysis.Convex.Slope
import Mathlib.Analysis.Convex.Topology
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.Baire.Lemmas
import Mathlib.Topology.Baire.CompleteMetrizable
import Mathlib.Tactic.Module
import Mathlib.Topology.Bases
import Def.Analysis.Convex.Straszewicz.Part3
/-!
# Straszewicz's theorem on exposed points

Every extreme point of a compact convex set in a finite-dimensional real
normed space lies in the closure of its exposed points.

Primary source: S. Straszewicz, "Über exponierte Punkte abgeschlossener
Punktmengen", Fundamenta Mathematicae 24 (1935), 139–143,
DOI 10.4064/FM-24-1-139-143.
-/


namespace Convex.Straszewicz

open Set Metric Filter TopologicalSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

variable {h : StrongDual ℝ E → ℝ} {x : StrongDual ℝ E}

section Support

variable {K : Set E}

omit [FiniteDimensional ℝ E] in
/-- The support function attains its value. -/
theorem suppFunc_attain (hK : IsCompact K) (hKne : K.Nonempty) (l : StrongDual ℝ E) :
    ∃ x ∈ K, l x = suppFunc K l := by
  have hcont : Continuous (fun x => l x) := (l : E →L[ℝ] ℝ).continuous
  have himg : IsCompact ((fun x => l x) '' K) := hK.image hcont
  have hne : ((fun x => l x) '' K).Nonempty := Set.image_nonempty.mpr hKne
  obtain ⟨x, hxK, hxl⟩ := IsCompact.sSup_mem himg hne
  exact ⟨x, hxK, hxl⟩

omit [FiniteDimensional ℝ E] in
/-- The support function is convex. -/
theorem suppFunc_convex (hK : IsCompact K) (hKne : K.Nonempty) :
    ConvexOn ℝ univ (suppFunc K) := by
  refine ⟨convex_univ, fun x _ y _ a b ha hb hab => ?_⟩
  have hcont : ∀ l : StrongDual ℝ E, Continuous (fun x => l x) := fun l =>
    (l : E →L[ℝ] ℝ).continuous
  have hbdd : ∀ l : StrongDual ℝ E, BddAbove ((fun x => l x) '' K) := fun l =>
    (hK.image (hcont l)).bddAbove
  apply csSup_le (Set.image_nonempty.mpr hKne)
  rintro z ⟨w, hwK, rfl⟩
  change (a • x + b • y) w ≤ a • suppFunc K x + b • suppFunc K y
  have hxw : x w ≤ suppFunc K x := le_csSup (hbdd x) ⟨w, hwK, rfl⟩
  have hyw : y w ≤ suppFunc K y := le_csSup (hbdd y) ⟨w, hwK, rfl⟩
  have e : (a • x + b • y) w = a * x w + b * y w := by
    simp [add_apply, smul_apply, smul_eq_mul]
  have hle : a * x w + b * y w ≤ a * suppFunc K x + b * suppFunc K y :=
    add_le_add (mul_le_mul_of_nonneg_left hxw ha) (mul_le_mul_of_nonneg_left hyw hb)
  rw [e]
  simp only [smul_eq_mul]
  exact hle

omit [FiniteDimensional ℝ E] in
/-- The support function is Lipschitz on bounded sets. -/
theorem suppFunc_lipschitz (hK : IsCompact K) (hKne : K.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ l₁ l₂ : StrongDual ℝ E,
      suppFunc K l₁ - suppFunc K l₂ ≤ C * ‖l₁ - l₂‖ := by
  obtain ⟨xB, hxBK, hBmax⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
  refine ⟨‖xB‖, norm_nonneg _, fun l₁ l₂ => ?_⟩
  obtain ⟨x₁, hx₁K, hx₁e⟩ := suppFunc_attain hK hKne l₁
  have hle1 : l₁ x₁ - l₂ x₁ ≤ ‖l₁ - l₂‖ * ‖xB‖ := by
    have e : l₁ x₁ - l₂ x₁ = (l₁ - l₂) x₁ := by rw [sub_apply]
    rw [e]
    calc (l₁ - l₂) x₁ ≤ ‖(l₁ - l₂) x₁‖ := le_abs_self _
      _ ≤ ‖l₁ - l₂‖ * ‖x₁‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖l₁ - l₂‖ * ‖xB‖ :=
          mul_le_mul_of_nonneg_left (hBmax hx₁K) (norm_nonneg _)
  have hle2 : l₂ x₁ ≤ suppFunc K l₂ :=
    le_csSup ((hK.image
      (show Continuous (fun x => l₂ x) from (l₂ : E →L[ℝ] ℝ).continuous))).bddAbove
      ⟨x₁, hx₁K, rfl⟩
  rw [← hx₁e]
  linarith

omit [FiniteDimensional ℝ E] in
/-- The support function is continuous. -/
theorem suppFunc_continuous (hK : IsCompact K) (hKne : K.Nonempty) :
    Continuous (suppFunc K) := by
  obtain ⟨C, hC, hlip⟩ := suppFunc_lipschitz hK hKne
  have hC1 : (0 : ℝ) < C + 1 := by linarith
  have hCε : ∀ ε : ℝ, 0 < ε → C * (ε / (C + 1)) ≤ ε := by
    intro ε hε
    rw [← mul_div_assoc, div_le_iff₀ hC1, mul_add, mul_one]
    linarith [mul_nonneg hC hε.le]
  rw [Metric.continuous_iff]
  intro l₀ ε hε
  refine ⟨ε / (C + 1), div_pos hε hC1, fun l hl => ?_⟩
  rw [dist_eq_norm] at hl
  have hmain : C * ‖l - l₀‖ < ε := by
    by_cases hC0 : C = 0
    · rw [hC0, zero_mul]
      exact hε
    · have hCpos : 0 < C := lt_of_le_of_ne' hC hC0
      calc C * ‖l - l₀‖ < C * (ε / (C + 1)) :=
              mul_lt_mul_of_pos_left hl hCpos
        _ ≤ ε := hCε ε hε
  have h1 := hlip l l₀
  have h2 := hlip l₀ l
  have hn : ‖l₀ - l‖ = ‖l - l₀‖ := by rw [← norm_neg, neg_sub]
  rw [dist_eq_norm, Real.norm_eq_abs, abs_lt]
  constructor
  · have h2' : suppFunc K l₀ - suppFunc K l ≤ C * ‖l - l₀‖ := by
      calc suppFunc K l₀ - suppFunc K l ≤ C * ‖l₀ - l‖ := h2
        _ = C * ‖l - l₀‖ := by rw [hn]
    linarith
  · calc suppFunc K l - suppFunc K l₀ ≤ C * ‖l - l₀‖ := h1
      _ < ε := hmain

end Support
end Convex.Straszewicz
