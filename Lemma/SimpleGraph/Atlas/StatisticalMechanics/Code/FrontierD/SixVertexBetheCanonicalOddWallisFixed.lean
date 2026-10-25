import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheCanonicalOddWallisFixed.Part3
open StatMech StatMech.FrontierD


/--
[abs_mul_cos_sub_sin_le_abs_cube_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma abs_mul_cos_sub_sin_le_abs_cube_div_two_eq
  {x : Real}
-- given
  (hx : |x| <= 1) :
-- imply
  |x * Real.cos x - Real.sin x| <= |x| ^ 3 / 2 := by
-- proof
  apply StatMech.FrontierD.abs_mul_cos_sub_sin_le_abs_cube_div_two hx

/--
[abs_sixVertexSincDerivative_le_abs_div_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma abs_sixVertexSincDerivative_le_abs_div_two_eq
  {x : Real}
-- given
  (hx : |x| <= 1) :
-- imply
  |sixVertexSincDerivative x| <= |x| / 2 := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexSincDerivative_le_abs_div_two hx

/--
[continuousAt_sixVertexSincDerivative_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma continuousAt_sixVertexSincDerivative_zero_eq :
-- imply
  ContinuousAt sixVertexSincDerivative 0 := by
-- proof
  apply StatMech.FrontierD.continuousAt_sixVertexSincDerivative_zero

/--
[continuous_sixVertexSincDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma continuous_sixVertexSincDerivative_eq :
-- imply
  Continuous sixVertexSincDerivative := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexSincDerivative

/--
[hasDerivAt_sixVertexBetheDesingularizedLogObservable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma hasDerivAt_sixVertexBetheDesingularizedLogObservable_eq
  {c x : Real}
-- given
  (hc : 2 < c)
  (hx : x ∈ Set.Icc 0 Real.pi) :
-- imply
  HasDerivAt (sixVertexBetheDesingularizedLogObservable c) (sixVertexBetheDesingularizedLogObservableDerivative c x) x := by
-- proof
  apply StatMech.FrontierD.hasDerivAt_sixVertexBetheDesingularizedLogObservable hc hx

/--
[continuousOn_sixVertexBetheDesingularizedLogObservableDerivative](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma continuousOn_sixVertexBetheDesingularizedLogObservableDerivative_eq
  {c : Real}
-- given
  (hc : 2 < c) :
-- imply
  ContinuousOn (sixVertexBetheDesingularizedLogObservableDerivative c) (Set.Icc 0 Real.pi) := by
-- proof
  apply StatMech.FrontierD.continuousOn_sixVertexBetheDesingularizedLogObservableDerivative hc

/--
[abs_intervalIntegral_sub_const_mul_le_of_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma abs_intervalIntegral_sub_const_mul_le_of_bound_eq
  {f : Real -> Real}
  {a b z E : Real}
-- given
  (hab : a <= b)
  (hf : ContinuousOn f (Set.Icc a b))
  (hE : 0 <= E)
  (hbound : ∀ x ∈ Set.Icc a b, |f x - z| <= E) :
-- imply
  |(∫ x in a..b, f x) - (b - a) * z| <= E * (b - a) := by
-- proof
  apply StatMech.FrontierD.abs_intervalIntegral_sub_const_mul_le_of_bound hab hf hE hbound

/--
[abs_two_halfIncrement_sub_fullIncrement_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma abs_two_halfIncrement_sub_fullIncrement_le_eq
  {H D : Real -> Real}
  {a b E : Real}
-- given
  (hab : a <= b)
  (hH : ContinuousOn H (Set.Icc a b))
  (hD : ContinuousOn D (Set.Icc a b))
  (hderiv : ∀ x ∈ Set.Icc a b, HasDerivAt H (D x) x)
  (hE : 0 <= E)
  (hclose : ∀ x ∈ Set.Icc a b, |D x - D ((a + b) / 2)| <= E) :
-- imply
  |2 * (H ((a + b) / 2) - H a) - (H b - H a)| <= E * (b - a) := by
-- proof
  apply StatMech.FrontierD.abs_two_halfIncrement_sub_fullIncrement_le hab hH hD hderiv hE hclose

/--
[abs_two_halfIncrementSum_sub_endpoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma abs_two_halfIncrementSum_sub_endpoint_le_eq
  {H D : Real -> Real}
  {n : Nat}
  {E : Real}
-- given
  (a : Nat -> Real)
  (ha : ∀ j, j <= n -> a j ∈ Set.Icc 0 Real.pi)
  (hordered : ∀ j, j < n -> a j <= a (j + 1))
  (hH : ContinuousOn H (Set.Icc 0 Real.pi))
  (hD : ContinuousOn D (Set.Icc 0 Real.pi))
  (hderiv : ∀ x ∈ Set.Icc 0 Real.pi, HasDerivAt H (D x) x)
  (hE : 0 <= E)
  (hclose : ∀ j, j < n -> ∀ x ∈ Set.Icc (a j) (a (j + 1)), |D x - D ((a j + a (j + 1)) / 2)| <= E) :
-- imply
  |2 * ∑ j : Fin n, (H ((a j.val + a (j.val + 1)) / 2) - H (a j.val)) - (H (a n) - H (a 0))| <= E * (a n - a 0) := by
-- proof
  apply StatMech.FrontierD.abs_two_halfIncrementSum_sub_endpoint_le a ha hordered hH hD hderiv hE hclose

/--
[sixVertexCanonicalOddHalfPartitionRoot_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfPartitionRoot_eq_eq
  {c : Real}
  {s k j : Nat}
-- given
  (hc : 2 < c)
  (hj : j < s + k + 2) :
-- imply
  sixVertexCanonicalOddHalfPartitionRoot hc s k j = sixVertexCanonicalDensityPerronPositiveHalfRoots hc (2 * s + 1 + k) ⟨j, by omega⟩ := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfPartitionRoot_eq hc s k j hj

/--
[sixVertexCanonicalOddHalfPartitionRoot_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfPartitionRoot_left_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddHalfPartitionRoot hc s k j.val = sixVertexCanonicalOddLeftHalfRoot hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfPartitionRoot_left hc s k j

/--
[sixVertexCanonicalOddHalfPartitionRoot_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfPartitionRoot_right_eq
  {c : Real}
  {s k : Nat}
  {j : Fin (s + k + 1)}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddHalfPartitionRoot hc s k (j.val + 1) = sixVertexCanonicalOddRightHalfRoot hc s k j := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfPartitionRoot_right hc s k j

/--
[sixVertexCanonicalOddHalfPartitionRoot_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma sixVertexCanonicalOddHalfPartitionRoot_last_eq
  {c : Real}
  {s k : Nat}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexCanonicalOddHalfPartitionRoot hc s k (s + k + 1) = sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddHalfPartitionRoot_last hc s k

/--
[sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower_eq
  {c : Real}
  {s k : Nat}
  {lower : Real}
-- given
  (hc : 2 < c)
  (hlower : 0 < lower)
  (hdensity : ∀ x, lower <= sixVertexFiniteRootDensity c (sixVertexFourWidth (2 * s + 1) k) ((2 * s + 1 + k + 1) + (2 * s + 1 + k + 1)) (sixVertexCanonicalDensityPerronBetheRoots hc (2 * s + 1 + k)) x) :
-- imply
  sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1)) <= 1 / (2 * (sixVertexFourWidth (2 * s + 1) k : Real) * lower) := by
-- proof
  apply StatMech.FrontierD.sixVertexCanonicalOddFirstLeftHalfRoot_le_of_densityLower hc s k hlower hdensity

/--
[tendsto_sixVertexCanonicalOddFirstLeftHalfRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddFirstLeftHalfRoot_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddFirstLeftHalfRoot hc s

/--
[tendsto_sixVertexCanonicalOddFixedHalfIncrementError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddFixedHalfIncrementError_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => 2 * ∑ j : Fin (s + k + 1), (sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddLeftHalfRoot hc s k j)) - (sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddBoundaryHalfRoot hc s k (0 : Fin (s + 1))) - sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddLeftHalfRoot hc s k (0 : Fin (s + k + 1))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddFixedHalfIncrementError hc s

/--
[tendsto_sixVertexCanonicalOddFixedHalfIncrement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheCanonicalOddWallisFixed.lean)
-/
@[path]
private lemma tendsto_sixVertexCanonicalOddFixedHalfIncrement_eq
  {c : Real}
  {s : Nat}
-- given
  (hc : 2 < c) :
-- imply
  Tendsto (fun k => 2 * ∑ j : Fin (s + k + 1), (sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddMidpointHalfRoot hc s k j) - sixVertexBetheDesingularizedLogObservable c (sixVertexCanonicalOddLeftHalfRoot hc s k j))) atTop (nhds (Real.log (Real.cosh (sixVertexAntiferroelectricLambda c)) + Real.log Real.pi - Real.log (c ^ 2))) := by
-- proof
  apply StatMech.FrontierD.tendsto_sixVertexCanonicalOddFixedHalfIncrement hc s


-- created on 2026-10-23
