import Mathlib
import sympy.Basic
import sympy.atlas.Algebra.MvPolynomial.Stable
open scoped BigOperators ComplexOrder
open upper half-plane. -/
open Filter MvPolynomial
open MvPolynomial
open MathlibExt.Algebra.MvPolynomialStable


/--
[derivative_univariateSpecialization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma derivative_univariateSpecialization_eq
  [CommRing R] [DecidableEq σ]
  {i : σ}
  {x : σ → R}
  {p : MvPolynomial σ R} :
-- imply
  univariateSpecialization i x (pderiv i p) =
    Polynomial.derivative (univariateSpecialization i x p) := by
-- proof
  apply MvPolynomial.derivative_univariateSpecialization i x p

/--
[eval_univariateSpecialization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma eval_univariateSpecialization_eq
  [CommRing R] [DecidableEq σ]
  {i : σ}
  {x : σ → R}
  {t : R}
  {p : MvPolynomial σ R} :
-- imply
  Polynomial.eval t (univariateSpecialization i x p) =
    MvPolynomial.eval (Function.update x i t) p := by
-- proof
  apply MvPolynomial.eval_univariateSpecialization i x t p

/--
[map_star_univariateSpecialization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma map_star_univariateSpecialization_eq
  [DecidableEq σ]
  {i : σ}
  {a : σ → ℂ}
  {p : MvPolynomial σ ℂ}
-- given
  (hp : MvPolynomial.map (starRingEnd ℂ) p = p)
  (ha : ∀ j, j ≠ i → (starRingEnd ℂ) (a j) = a j) :
-- imply
  Polynomial.map (starRingEnd ℂ) (univariateSpecialization i a p) =
    univariateSpecialization i a p := by
-- proof
  apply MvPolynomial.map_star_univariateSpecialization i a p hp ha

/--
[_root_.MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_IsStable_roots_im_nonpos_univariateSpecialization_eq
  [DecidableEq σ]
  {p : MvPolynomial σ ℂ}
  {i : σ}
  {a : σ → ℂ}
-- given
  (hp : p.IsStable)
  (ha : ∀ j, j ≠ i → 0 ≤ (a j).im)
  (hq : univariateSpecialization i a p ≠ 0) :
-- imply
  ∀ w ∈ (univariateSpecialization i a p).roots, w.im ≤ 0 := by
-- proof
  apply MvPolynomial.IsStable.roots_im_nonpos_univariateSpecialization hp i a ha hq

/--
[_root_.MvPolynomial.isRealRooted_univariateSpecialization_of_isRealStable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_isRealRooted_univariateSpecialization_of_isRealStable_eq
  [DecidableEq σ]
  {i : σ}
  {p : MvPolynomial σ ℂ}
  {d : ℕ}
  {a : σ → ℂ}
-- given
  (hp : p.IsRealStable)
  (hmonic : ∀ x, (univariateSpecialization i x p).Monic)
  (hdegree : ∀ x, (univariateSpecialization i x p).natDegree = d)
  (ha : ∀ j, j ≠ i → (a j).im = 0) :
-- imply
  (univariateSpecialization i a p).IsRealRooted := by
-- proof
  apply MvPolynomial.isRealRooted_univariateSpecialization_of_isRealStable i p hp d hmonic hdegree a ha

/--
[_root_.MvPolynomial.IsStable.sub_pderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_IsStable_sub_pderiv_eq
  {p : MvPolynomial σ ℂ}
  {i : σ}
-- given
  (hp : p.IsStable) :
-- imply
  (p - pderiv i p).IsStable := by
-- proof
  apply MvPolynomial.IsStable.sub_pderiv hp i

/--
[_root_.MvPolynomial.IsRealStable.sub_pderiv](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_IsRealStable_sub_pderiv_eq
  {p : MvPolynomial σ ℂ}
  {i : σ}
-- given
  (hp : p.IsRealStable) :
-- imply
  (p - pderiv i p).IsRealStable := by
-- proof
  apply MvPolynomial.IsRealStable.sub_pderiv hp i

/--
[_root_.MvPolynomial.IsStable.mixedDifferential](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_IsStable_mixedDifferential_eq
  {p : MvPolynomial σ ℂ}
  {indices : List σ}
-- given
  (hp : p.IsStable) :
-- imply
  (MvPolynomial.mixedDifferential indices p).IsStable := by
-- proof
  apply MvPolynomial.IsStable.mixedDifferential hp indices

/--
[_root_.MvPolynomial.IsRealStable.mixedDifferential](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Algebra/MvPolynomial/Stable.lean)
-/
@[path]
private lemma MvPolynomial_IsRealStable_mixedDifferential_eq
  {p : MvPolynomial σ ℂ}
  {indices : List σ}
-- given
  (hp : p.IsRealStable) :
-- imply
  (MvPolynomial.mixedDifferential indices p).IsRealStable := by
-- proof
  apply MvPolynomial.IsRealStable.mixedDifferential hp indices


-- created on 2026-10-20
