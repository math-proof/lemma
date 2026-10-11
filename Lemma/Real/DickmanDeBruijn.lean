import Mathlib
import sympy.Basic
import sympy.functions.special.DickmanDeBruijn


/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_eq_zero_of_neg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : u < 0) :
-- imply
  ρ u = 0 := by
-- proof
  apply Real.IsDickmanDeBruijn.eq_zero_of_neg h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_maps_to_ici_icc_is
-- given
  (ρ : ℝ → ℝ)
  (h : Real.IsDickmanDeBruijn ρ) :
-- imply
  Set.MapsTo ρ (Set.Ici (0 : ℝ)) (Set.Icc (0 : ℝ) 1) := by
-- proof
  apply Real.IsDickmanDeBruijn.mapsTo_Ici_Icc h

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_continuous_on_ici_is
-- given
  (ρ : ℝ → ℝ)
  (h : Real.IsDickmanDeBruijn ρ) :
-- imply
  ContinuousOn ρ (Set.Ici (0 : ℝ)) := by
-- proof
  apply Real.IsDickmanDeBruijn.continuousOn_Ici h

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_eq_one_of_mem_icc
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : u ∈ Set.Icc (0 : ℝ) 1) :
-- imply
  ρ u = 1 := by
-- proof
  apply Real.IsDickmanDeBruijn.eq_one_of_mem_Icc h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_eq_one_of_nonneg_of_le_one
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (h0 : 0 ≤ u)
  (h1 : u ≤ 1) :
-- imply
  ρ u = 1 := by
-- proof
  apply Real.IsDickmanDeBruijn.eq_one_of_nonneg_of_le_one h h0 h1

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_differentiable_at_of_one_lt_is
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 1 < u) :
-- imply
  DifferentiableAt ℝ ρ u := by
-- proof
  apply Real.IsDickmanDeBruijn.differentiableAt_of_one_lt h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_delay_eq
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 1 < u) :
-- imply
  u * deriv ρ u + ρ (u - 1) = 0 := by
-- proof
  apply Real.IsDickmanDeBruijn.delay_eq h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_nonneg_of_nonneg_le
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  0 ≤ ρ u := by
-- proof
  apply Real.IsDickmanDeBruijn.nonneg_of_nonneg h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_le_one_of_nonneg
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  ρ u ≤ 1 := by
-- proof
  apply Real.IsDickmanDeBruijn.le_one_of_nonneg h hu

/--
[DickmanDeBruijn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/DickmanDeBruijn.lean)
-/
@[path]
private lemma is_dickman_de_bruijn_mem_icc_of_nonneg_is
-- given
  (ρ : ℝ → ℝ)
  (u : ℝ)
  (h : Real.IsDickmanDeBruijn ρ)
  (hu : 0 ≤ u) :
-- imply
  ρ u ∈ Set.Icc (0 : ℝ) 1 := by
-- proof
  apply Real.IsDickmanDeBruijn.mem_Icc_of_nonneg h hu


-- created on 2026-10-11
