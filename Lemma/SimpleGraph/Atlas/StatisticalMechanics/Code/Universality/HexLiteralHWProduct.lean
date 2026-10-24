import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexLiteralHWProduct
open StatMech StatMech.Universality


/--
[hlhp_finite_partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWProduct.lean)
-/
@[path]
private lemma hlhp_finite_partial_bound_eq
  {a : ℂ}
  {N : ℕ}
  {x : ℝ}
  {ups : ℕ → ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x)
  (hups : ∀ T, 0 ≤ ups T)
  (hmul : Multipliable (fun T => 1 + ups T))
  (hlower : ∀ T, hchb_bridgeMass (hlha_augmentedTwoHalfData a h0 N).lowerImage x T ≤ ups T)
  (hupper : ∀ T, hchb_bridgeMass (hlha_augmentedTwoHalfData a h0 N).upperImage x T ≤ ups T) :
-- imply
  ∑ n ∈ Finset.range N, (hlc_sawCount a h0 n : ℝ) * x ^ n ≤ (x ^ 2)⁻¹ * (∏' T, (1 + ups T)) ^ 2 := by
-- proof
  apply StatMech.Universality.hlhp_finite_partial_bound a h0 N hx ups hups hmul hlower hupper

/--
[hlhp_summable_of_content_masses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexLiteralHWProduct.lean)
-/
@[path]
private lemma hlhp_summable_of_content_masses_eq
  {a : ℂ}
  {x : ℝ}
  {ups : ℕ → ℝ}
-- given
  (h0 : ℤ)
  (hx : 0 < x)
  (hups : ∀ T, 0 ≤ ups T)
  (hsum : Summable ups)
  (hlower : ∀ N T, hchb_bridgeMass (hlha_augmentedTwoHalfData a h0 N).lowerImage x T ≤ ups T)
  (hupper : ∀ N T, hchb_bridgeMass (hlha_augmentedTwoHalfData a h0 N).upperImage x T ≤ ups T) :
-- imply
  Summable (fun n => hlc_sawCountR a h0 n * x ^ n) := by
-- proof
  apply StatMech.Universality.hlhp_summable_of_content_masses a h0 hx ups hups hsum hlower hupper


-- created on 2026-10-23
