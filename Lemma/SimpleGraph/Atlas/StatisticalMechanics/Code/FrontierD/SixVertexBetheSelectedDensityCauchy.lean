import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheSelectedDensityCauchy
open Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexRootDensityWeight_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma sixVertexRootDensityWeight_lower_eq
  {c : Real}
  {x : Real}
-- given
  (hc : 2 < c) :
-- imply
  (sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c <= sixVertexRootDensityWeight c x := by
-- proof
  apply StatMech.FrontierD.sixVertexRootDensityWeight_lower hc x

/--
[sixVertexSelectedFiniteRootDensity_weighted_cauchy_direct_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma sixVertexSelectedFiniteRootDensity_weighted_cauchy_direct_tail_eq
  {c : Real}
  {k l : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |sixVertexRootDensityWeight c x * (sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) x - sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l) ((l + 1) + (l + 1)) (sixVertexHalfFilledBetheRoots hc l) x)| <= sixVertexSelectedDensityCauchyError c k l := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedFiniteRootDensity_weighted_cauchy_direct_tail hc htail k l

/--
[sixVertexSelectedObservableQuadratureError_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma sixVertexSelectedObservableQuadratureError_tendsto_zero_eq
  {c : Real}
  {C : NNReal}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (sixVertexSelectedObservableQuadratureError c C) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedObservableQuadratureError_tendsto_zero hc htail C

/--
[sixVertexSelectedObservableCauchyControl_tendsto_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma sixVertexSelectedObservableCauchyControl_tendsto_zero_eq
  {c : Real}
  {C : NNReal}
  {B : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c) :
-- imply
  Tendsto (sixVertexSelectedObservableCauchyControl c C B) atTop (nhds 0) := by
-- proof
  apply StatMech.FrontierD.sixVertexSelectedObservableCauchyControl_tendsto_zero hc htail C B

/--
[abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail_eq
  {c : Real}
  {f : Real -> Real}
  {C : NNReal}
  {k : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi)) :
-- imply
  |sixVertexSelectedEmpiricalObservable hc f k - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) y| <= sixVertexSelectedObservableQuadratureError c C k := by
-- proof
  apply StatMech.FrontierD.abs_sixVertexSelectedEmpiricalObservable_sub_finiteDensityIntegral_le_tail hc htail hf hlip hperiodic k

/--
[abs_selectedFiniteDensityIntegral_sub_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma abs_selectedFiniteDensityIntegral_sub_le_tail_eq
  {c : Real}
  {f : Real -> Real}
  {B : Real}
  {k l : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hf : Continuous f)
  (hB : 0 <= B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B) :
-- imply
  |(∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 k) ((k + 1) + (k + 1)) (sixVertexHalfFilledBetheRoots hc k) y) - ∫ y in -Real.pi..Real.pi, f y * sixVertexFiniteRootDensity c (sixVertexFourWidth 0 l) ((l + 1) + (l + 1)) (sixVertexHalfFilledBetheRoots hc l) y| <= B * (sixVertexSelectedDensityCauchyError c k l / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) * (2 * Real.pi) := by
-- proof
  apply StatMech.FrontierD.abs_selectedFiniteDensityIntegral_sub_le_tail hc htail hf hB hfBound k l

/--
[abs_selectedEmpiricalObservable_sub_le_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma abs_selectedEmpiricalObservable_sub_le_tail_eq
  {c : Real}
  {f : Real -> Real}
  {C : NNReal}
  {B : Real}
  {k l : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi))
  (hB : 0 <= B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B) :
-- imply
  |sixVertexSelectedEmpiricalObservable hc f k - sixVertexSelectedEmpiricalObservable hc f l| <= sixVertexSelectedObservableQuadratureError c C k + B * (sixVertexSelectedDensityCauchyError c k l / ((sixVertexAnisotropyMagnitude c - 1) / sixVertexRootDensityScale c)) * (2 * Real.pi) + sixVertexSelectedObservableQuadratureError c C l := by
-- proof
  apply StatMech.FrontierD.abs_selectedEmpiricalObservable_sub_le_tail hc htail hf hlip hperiodic hB hfBound k l

/--
[abs_selectedEmpiricalObservable_sub_le_cauchyControl_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma abs_selectedEmpiricalObservable_sub_le_cauchyControl_tail_eq
  {c : Real}
  {f : Real -> Real}
  {C : NNReal}
  {B : Real}
  {k l : Nat}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi))
  (hB : 0 <= B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B) :
-- imply
  |sixVertexSelectedEmpiricalObservable hc f k - sixVertexSelectedEmpiricalObservable hc f l| <= sixVertexSelectedObservableCauchyControl c C B k + sixVertexSelectedObservableCauchyControl c C B l := by
-- proof
  apply StatMech.FrontierD.abs_selectedEmpiricalObservable_sub_le_cauchyControl_tail hc htail hf hlip hperiodic hB hfBound k l

/--
[exists_tendsto_sixVertexSelectedEmpiricalObservable_tail](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheSelectedDensityCauchy.lean)
-/
@[path]
private lemma exists_tendsto_sixVertexSelectedEmpiricalObservable_tail_eq
  {c : Real}
  {f : Real -> Real}
  {C : NNReal}
  {B : Real}
-- given
  (hc : 2 < c)
  (htail : 2 < sixVertexAnisotropyMagnitude c)
  (hf : Continuous f)
  (hlip : LipschitzWith C f)
  (hperiodic : Function.Periodic f (2 * Real.pi))
  (hB : 0 <= B)
  (hfBound : ∀ x ∈ Set.Icc (-Real.pi) Real.pi, |f x| <= B) :
-- imply
  ∃ a : Real, Tendsto (sixVertexSelectedEmpiricalObservable hc f) atTop (nhds a) := by
-- proof
  apply StatMech.FrontierD.exists_tendsto_sixVertexSelectedEmpiricalObservable_tail hc htail hf hlip hperiodic hB hfBound


-- created on 2026-10-23
