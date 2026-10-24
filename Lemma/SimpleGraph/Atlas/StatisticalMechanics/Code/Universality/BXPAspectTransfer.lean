import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.BXPAspectTransfer
open Set MeasureTheory SimpleGraph StatMech StatMech.Universality


/--
[bat_swapConfig_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_swapConfig_involutive_eq
  {ω : ConfigSpace (Sym2 (Site 2))} :
-- imply
  crf_swapConfig (crf_swapConfig ω) = ω := by
-- proof
  apply StatMech.Universality.bat_swapConfig_involutive ω

/--
[bat_horizontal_to_vertical_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_horizontal_to_vertical_swap_eq
  {a b c d : ℤ}
  {ω : ConfigSpace (Sym2 (Site 2))}
-- given
  (h : HorizontalCrossing ω a b c d) :
-- imply
  VerticalCrossing (crf_swapConfig ω) c d a b := by
-- proof
  apply StatMech.Universality.bat_horizontal_to_vertical_swap a b c d ω h

/--
[bat_translatedHorizontal_eq_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_translatedHorizontal_eq_physical_eq
  {τ : Site 2}
  {a b : ℤ} :
-- imply
  translatedHorizontalCrossingEvent τ a b = horizontalCrossingEvent (τ 0) (a + τ 0) (τ 1) (b + τ 1) := by
-- proof
  apply StatMech.Universality.bat_translatedHorizontal_eq_physical τ a b

/--
[bat_translatedVertical_eq_physical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_translatedVertical_eq_physical_eq
  {τ : Site 2}
  {a b : ℤ} :
-- imply
  translatedVerticalCrossingEvent τ a b = verticalCrossingEvent (τ 0) (a + τ 0) (τ 1) (b + τ 1) := by
-- proof
  apply StatMech.Universality.bat_translatedVertical_eq_physical τ a b

/--
[bat_verticalIntersection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_verticalIntersection_eq
  {ω : ConfigSpace (Sym2 (Site 2))}
  {a b c m m' d : ℤ}
-- given
  (hab : a ≤ b)
  (hcm : c ≤ m)
  (hmm' : m ≤ m')
  (hm'd : m' ≤ d)
  (hcm' : c < m')
  (hmd : m < d) :
-- imply
  VerticalCrossing ω a b c m' → HorizontalCrossing ω a b m m' → VerticalCrossing ω a b m d → VerticalCrossing ω a b c d := by
-- proof
  apply StatMech.Universality.bat_verticalIntersection ω hab hcm hmm' hm'd hcm' hmd

/--
[bat_vertical_strip_glue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_vertical_strip_glue_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {a b c m m' d : ℤ}
-- given
  (hpa : PositivelyAssociated μ)
  (hab : a ≤ b)
  (hcm : c ≤ m)
  (hmm' : m ≤ m')
  (hm'd : m' ≤ d)
  (hcm' : c < m')
  (hmd : m < d) :
-- imply
  μ.real (verticalCrossingEvent a b c m') * μ.real (horizontalCrossingEvent a b m m') * μ.real (verticalCrossingEvent a b m d) ≤ μ.real (verticalCrossingEvent a b c d) := by
-- proof
  apply StatMech.Universality.bat_vertical_strip_glue μ hpa hab hcm hmm' hm'd hcm' hmd

/--
[bat_horizontal_lower_of_bxp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_horizontal_lower_of_bxp_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 n : ℕ}
  {τ : Site 2}
-- given
  (hn : n0 ≤ n) :
-- imply
  boxCrossingInf μ ρ n0 ≤ μ.real (translatedHorizontalCrossingEvent τ ⌊ρ * (n : ℝ)⌋ (n : ℤ)) := by
-- proof
  apply StatMech.Universality.bat_horizontal_lower_of_bxp τ hn

/--
[bat_vertical_lower_of_bxp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_vertical_lower_of_bxp_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  {ρ : ℝ}
  {n0 n : ℕ}
  {τ : Site 2}
-- given
  (hn : n0 ≤ n) :
-- imply
  boxCrossingInf μ ρ n0 ≤ μ.real (translatedVerticalCrossingEvent τ (n : ℤ) ⌊ρ * (n : ℝ)⌋) := by
-- proof
  apply StatMech.Universality.bat_vertical_lower_of_bxp τ hn

/--
[bat_horizontal_physical_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_horizontal_physical_mono_eq
  {τ : Site 2}
  {w w' h : ℤ}
-- given
  (hw : 0 < w)
  (hww' : w ≤ w') :
-- imply
  horizontalCrossingEvent (τ 0) (w' + τ 0) (τ 1) (h + τ 1) ⊆ horizontalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h + τ 1) := by
-- proof
  apply StatMech.Universality.bat_horizontal_physical_mono hw hww'

/--
[bat_vertical_physical_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_vertical_physical_mono_eq
  {τ : Site 2}
  {w h h' : ℤ}
-- given
  (hh : 0 < h)
  (hh' : h ≤ h') :
-- imply
  verticalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h' + τ 1) ⊆ verticalCrossingEvent (τ 0) (w + τ 0) (τ 1) (h + τ 1) := by
-- proof
  apply StatMech.Universality.bat_vertical_physical_mono hh hh'

/--
[bat_horizontal_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_horizontal_chain_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {c : ℝ}
  {n W : ℕ}
  {τ : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hc : 0 ≤ c)
  (hn : 1 ≤ n)
  (hW : n < W)
  (hH : ∀ σ : Site 2, c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)))
  (hV : ∀ σ : Site 2, c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ))) :
-- imply
  ∀ k : ℕ, 1 ≤ k → c ^ (2 * k - 1) ≤ μ.real (horizontalCrossingEvent (τ 0) ((n + k * (W - n) : ℕ) + τ 0) (τ 1) ((n : ℤ) + τ 1)) := by
-- proof
  apply StatMech.Universality.bat_horizontal_chain μ hpa c hc n W hn hW τ hH hV

/--
[bat_vertical_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma bat_vertical_chain_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {c : ℝ}
  {n W : ℕ}
  {τ : Site 2}
-- given
  (hpa : PositivelyAssociated μ)
  (hc : 0 ≤ c)
  (hn : 1 ≤ n)
  (hW : n < W)
  (hH : ∀ σ : Site 2, c ≤ μ.real (translatedHorizontalCrossingEvent σ (W : ℤ) (n : ℤ)))
  (hV : ∀ σ : Site 2, c ≤ μ.real (translatedVerticalCrossingEvent σ (n : ℤ) (W : ℤ))) :
-- imply
  ∀ k : ℕ, 1 ≤ k → c ^ (2 * k - 1) ≤ μ.real (verticalCrossingEvent (τ 0) ((n : ℤ) + τ 0) (τ 1) ((n + k * (W - n) : ℕ) + τ 1)) := by
-- proof
  apply StatMech.Universality.bat_vertical_chain μ hpa c hc n W hn hW τ hH hV

/--
[boxCrossingProperty_aspect_independent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/BXPAspectTransfer.lean)
-/
@[path]
private lemma boxCrossingProperty_aspect_independent_eq
  {μ : Measure (ConfigSpace (Sym2 (Site 2)))}
  [IsProbabilityMeasure μ]
  {ρ : ℝ}
-- given
  (hpa : PositivelyAssociated μ)
  (hρBXP : BoxCrossingProperty μ ρ) :
-- imply
  ∀ ρ' : ℝ, 1 < ρ' → BoxCrossingProperty μ ρ' := by
-- proof
  apply StatMech.Universality.boxCrossingProperty_aspect_independent μ hpa hρBXP


-- created on 2026-10-23
