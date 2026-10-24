import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheLogRegularizationCutoff
open StatMech StatMech.FrontierD


/--
[hasDerivAt_sixVertexBetheLogRegularizationError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheLogRegularizationError_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  HasDerivAt (sixVertexBetheLogRegularizationError c epsilon) (sixVertexBetheLogNormDerivative c x - sixVertexRegularizedBetheLogNormDerivative c epsilon x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheLogRegularizationError hc hepsilon hx hxIcc

/--
[abs_sixVertexBetheLogRegularizationError_derivative_le_singular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogRegularizationError_derivative_le_singular_eq
  {c epsilon x : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hx : x ≠ 0)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi) :
-- imply
  |sixVertexBetheLogNormDerivative c x - sixVertexRegularizedBetheLogNormDerivative c epsilon x| <= Real.pi / |x| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogRegularizationError_derivative_le_singular hc hepsilon hx hxIcc

/--
[abs_sixVertexBetheLogRegularizationError_derivative_le_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogRegularizationError_derivative_le_far_eq
  {c epsilon x delta : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hdelta : 0 < delta)
  (hxIcc : x ∈ Set.Icc (-Real.pi) Real.pi)
  (hx : delta <= |x|) :
-- imply
  |sixVertexBetheLogNormDerivative c x - sixVertexRegularizedBetheLogNormDerivative c epsilon x| <= epsilon * Real.pi ^ 4 / (16 * delta ^ 4) := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogRegularizationError_derivative_le_far hc hepsilon hdelta hxIcc hx

/--
[abs_sixVertexBetheLogRegularizationError_sub_le_singular](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogRegularizationError_sub_le_singular_eq
  {c epsilon p q : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hp : p ∈ Set.Ioo 0 Real.pi)
  (hq : q ∈ Set.Ioo 0 Real.pi)
  (hclose : |q - p| <= p / 2) :
-- imply
  |sixVertexBetheLogRegularizationError c epsilon q - sixVertexBetheLogRegularizationError c epsilon p| <= (2 * Real.pi / p) * |q - p| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogRegularizationError_sub_le_singular hc hepsilon hp hq hclose

/--
[abs_sixVertexBetheLogRegularizationError_sub_le_far](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma abs_sixVertexBetheLogRegularizationError_sub_le_far_eq
  {c epsilon delta p q : Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hdelta : 0 < delta)
  (hp : p ∈ Set.Ioo 0 Real.pi)
  (hq : q ∈ Set.Ioo 0 Real.pi)
  (hpFar : delta <= p)
  (hclose : |q - p| <= p / 2) :
-- imply
  |sixVertexBetheLogRegularizationError c epsilon q - sixVertexBetheLogRegularizationError c epsilon p| <= (epsilon * Real.pi ^ 4 / delta ^ 4) * |q - p| := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexBetheLogRegularizationError_sub_le_far hc hepsilon hdelta hp hq hpFar hclose

/--
[abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff_eq
  {c epsilon delta C : Real}
  {N n T : Nat}
  {p q : Fin n -> Real}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hdelta : 0 < delta)
  (hC : 0 <= C)
  (hN : 0 < N)
  (hp : forall j, p j ∈ Set.Ioo 0 Real.pi)
  (hq : forall j, q j ∈ Set.Ioo 0 Real.pi)
  (hclose : forall j, |q j - p j| <= p j / 2)
  (hdiff : forall j, |q j - p j| <= C * p j / N)
  (hfar : forall j, T <= j.val -> delta <= p j) :
-- imply
  |∑ j, (sixVertexBetheLogRegularizationError c epsilon (q j) - sixVertexBetheLogRegularizationError c epsilon (p j))| <= (T : Real) * (2 * Real.pi * C / N) + (n : Real) * ((epsilon * Real.pi ^ 4 / delta ^ 4) * (C * Real.pi / N)) := by
-- proof
  apply StatMech.FrontierD.abs_sum_sixVertexBetheLogRegularizationError_sub_le_cutoff hc hepsilon hdelta hC hN hp hq hclose hdiff hfar

/--
[eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s) k let n := s + k + 1 let C := sixVertexCanonicalEvenOffsetLinearBound c hc s |∑ j : Fin n, (sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| <= ((N / M + 1 : Nat) : Real) * (2 * Real.pi * C / N) + (n : Real) * ((epsilon * Real.pi ^ 4 / (2 * Real.pi / M) ^ 4) * (C * Real.pi / N)) := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le hc hepsilon s hM

/--
[eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple_eq
  {c epsilon : Real}
  {s : Nat}
  {M : Nat}
-- given
  (hc : 2 < c)
  (hepsilon : 0 < epsilon)
  (hM : 0 < M) :
-- imply
  ∀ᶠ k : Nat in atTop, let N := sixVertexFourWidth (2 * s) k let n := s + k + 1 let C := sixVertexCanonicalEvenOffsetLinearBound c hc s |∑ j : Fin n, (sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| <= 2 * Real.pi * C * (1 / M + 1 / N) + epsilon * C * Real.pi * M ^ 4 / 16 := by
-- proof
  apply StatMech.FrontierD.eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_le_simple hc hepsilon s hM

/--
[exists_eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_lt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheLogRegularizationCutoff.lean)
-/
@[path]
private lemma exists_eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_lt_eq
  {c : Real}
  {s : Nat}
  {eta : Real}
-- given
  (hc : 2 < c)
  (heta : 0 < eta) :
-- imply
  ∃ epsilon : Real, 0 < epsilon ∧ ∀ᶠ k : Nat in atTop, |∑ j : Fin (s + k + 1), (sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalFixedEvenDensityPositiveRoots hc s k j) - sixVertexBetheLogRegularizationError c epsilon (sixVertexCanonicalEvenCommonHalfRoot hc s k j))| < eta := by
-- proof
  apply StatMech.FrontierD.exists_eventually_abs_sum_sixVertexCanonicalEvenLogRegularizationError_lt hc s heta


-- created on 2026-10-23
