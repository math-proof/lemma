import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.IsingFermionicAxisStaircaseApproximation
open Filter Set Topology StatMech StatMech.Universality


/--
[eventually_norm_sub_lt_on_compact_of_tendstoLocallyUniformlyOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean)
-/
@[path]
private lemma eventually_norm_sub_lt_on_compact_of_tendstoLocallyUniformlyOn_eq
  {p : Filter ι}
  {F : ι -> Complex -> Complex}
  {f : Complex -> Complex}
  {K : Set Complex}
  {epsilon : Real}
-- given
  (h : TendstoLocallyUniformlyOn F f p Set.univ)
  (hK : IsCompact K)
  (hepsilon : 0 < epsilon) :
-- imply
  ∀ᶠ n in p, forall z, z ∈ K -> norm (F n z - f z) < epsilon := by
-- proof
  apply StatMech.Universality.eventually_norm_sub_lt_on_compact_of_tendstoLocallyUniformlyOn h K hK epsilon hepsilon

/--
[isConservativeOn_univ_of_ordered_wedgeContour_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean)
-/
@[path]
private lemma isConservativeOn_univ_of_ordered_wedgeContour_eq_zero_eq
-- given
  (f : Complex -> Complex)
  (hordered : forall z w : Complex, z.re <= w.re -> z.im <= w.im -> Complex.wedgeIntegral z w f + Complex.wedgeIntegral w z f = 0) :
-- imply
  Complex.IsConservativeOn f Set.univ := by
-- proof
  apply StatMech.Universality.isConservativeOn_univ_of_ordered_wedgeContour_eq_zero f hordered

/--
[norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean)
-/
@[path]
private lemma norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation_eq
  {x y mesh epsilon : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (width height : Nat)
  (hmesh : 0 < mesh)
  (hepsilon : 0 <= epsilon)
  (hosc : forall a, a ∈ axisTwoEdgeStaircaseBaseSet x y mesh width height -> forall q : Complex, norm (q - a) <= 2 * mesh -> norm (f q - f a) <= epsilon) :
-- imply
  norm (axisTwoEdgeStaircasePathIntegral f x y mesh width height - axisMacroDirectContour f x y mesh width height) <= 8 * epsilon * mesh * ((width + height : Nat) : Real) := by
-- proof
  apply StatMech.Universality.norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_of_baseOscillation f hf x y mesh epsilon width height hmesh hepsilon hosc

/--
[norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_baseError](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean)
-/
@[path]
private lemma norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_baseError_eq
  {x y mesh : Real}
  {epsilon : Real}
-- given
  (F G : Complex -> Complex)
  (hF : Continuous F)
  (hG : Continuous G)
  (width height : Nat)
  (hmesh : 0 < mesh)
  (hepsilon : 0 <= epsilon)
  (herror : forall a, a ∈ axisTwoEdgeStaircaseBaseSet x y mesh width height -> forall q : Complex, norm (q - a) <= 2 * mesh -> norm (F q - G q) <= epsilon) :
-- imply
  norm (axisTwoEdgeStaircasePathIntegral F x y mesh width height - axisTwoEdgeStaircasePathIntegral G x y mesh width height) <= 4 * epsilon * mesh * ((width + height : Nat) : Real) := by
-- proof
  apply StatMech.Universality.norm_axisTwoEdgeStaircasePathIntegral_sub_le_of_baseError F G hF hG x y mesh width height epsilon hmesh hepsilon herror

/--
[norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicAxisStaircaseApproximation.lean)
-/
@[path]
private lemma norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le_eq
  {x y mesh epsilon : Real}
-- given
  (f : Complex -> Complex)
  (hf : Continuous f)
  (width height : Nat)
  (hmesh : 0 < mesh)
  (hosc : forall a q : Complex, norm (q - a) <= 2 * mesh -> norm (f q - f a) <= epsilon) :
-- imply
  norm (axisTwoEdgeStaircasePathIntegral f x y mesh width height - axisMacroDirectContour f x y mesh width height) <= 8 * epsilon * mesh * ((width + height : Nat) : Real) := by
-- proof
  apply StatMech.Universality.norm_axisTwoEdgeStaircasePathIntegral_sub_axisMacroDirectContour_le f hf x y mesh epsilon width height hmesh hosc


-- created on 2026-10-23
