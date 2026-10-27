import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.v1.Atlas.DifferentialAnalysis.code.ConvolutionWellDefined
open MeasureTheory Set ConeSupport
open scoped SchwartzMap


namespace ConeSupport

/--
[convolution_decomp_well_defined_direct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/ConvolutionWellDefined.lean)
-/
@[path]
lemma convolution_decomp_well_defined_direct
  {n : ℕ}
  {u : 𝓢'(E n, ℂ)}
  {convSchwartz : 𝓢(E n, ℂ) → 𝓢'(E n, ℂ)}
  {convCompact : 𝓢'(E n, ℂ) → 𝓢'(E n, ℂ)}
  {d₁ d₂ : SchwartzCompactDecomp u}
-- given
  (hu : ConicSingularSupportSphere u = ∅)
  (hSchwartz_add : ∀ φ₁ φ₂ : 𝓢(E n, ℂ), convSchwartz (φ₁ + φ₂) = convSchwartz φ₁ + convSchwartz φ₂)
  (hCompact_add : ∀ u₁ u₂ : 𝓢'(E n, ℂ), convCompact (u₁ + u₂) = convCompact u₁ + convCompact u₂)
  (hcompat : ∀ φ : 𝓢(E n, ℂ), IsCompactlySupportedDistribution (schwEmbed φ) → convSchwartz φ = convCompact (schwEmbed φ)) :
-- imply
  convSchwartz d₁.schwartzPart + convCompact d₁.compactPart = convSchwartz d₂.schwartzPart + convCompact d₂.compactPart := by
-- proof
  set f₁ := d₁.schwartzPart
  set f₂ := d₂.schwartzPart
  set g₁ := d₁.compactPart
  set g₂ := d₂.compactPart
  have hdecomp : schwEmbed f₁ + g₁ = schwEmbed f₂ + g₂ := by
    rw [← d₁.sum_eq, ← d₂.sum_eq]
  have hCss := hasEmptyConicSingularSupportSphere_of_eq_empty u hu
  have hw : IsCompactlySupportedDistribution (schwEmbed (f₁ - f₂)) := by
    rw [map_sub]; exact hCss.diff_compactlySupported d₁ d₂
  have hg₂ : g₂ = schwEmbed (f₁ - f₂) + g₁ := by
    have h : schwEmbed f₁ + g₁ - schwEmbed f₂ = g₂ := by rw [hdecomp]; abel
    show g₂ = schwEmbed (f₁ - f₂) + g₁
    rw [map_sub, ← h]; abel
  have step1 : convSchwartz f₁ = convSchwartz f₂ + convSchwartz (f₁ - f₂) := by
    have h := hSchwartz_add f₂ (f₁ - f₂)
    simp only [add_sub_cancel] at h
    exact h
  have step2 : convSchwartz (f₁ - f₂) = convCompact (schwEmbed (f₁ - f₂)) :=
    hcompat _ hw
  have step3 : convCompact g₂ =
    convCompact (schwEmbed (f₁ - f₂)) + convCompact g₁ := by
    rw [hg₂, hCompact_add]
  calc convSchwartz f₁ + convCompact g₁
    = (convSchwartz f₂ + convSchwartz (f₁ - f₂)) + convCompact g₁ := by rw [step1]
    _ = (convSchwartz f₂ + convCompact (schwEmbed (f₁ - f₂))) + convCompact g₁ := by
      rw [step2]
    _ = convSchwartz f₂ + (convCompact (schwEmbed (f₁ - f₂)) + convCompact g₁) := by
      rw [add_assoc]
    _ = convSchwartz f₂ + convCompact g₂ := by rw [← step3]
end ConeSupport



-- created on 2026-10-23
