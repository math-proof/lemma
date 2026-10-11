import Mathlib
import sympy.Basic
import sympy.series.formal.Multivariate


/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma coeff_embed_univ_in_biv_eq
-- given
  {R : Type*} [CommSemiring R] (f : ℕ → PowerSeries R) (n k : ℕ) :
-- imply
  (AlgebraicCombinatorics.embedUnivInBiv f) (Finsupp.single 0 n + Finsupp.single 1 k) =
    (f k).coeff n := by
-- proof
  apply AlgebraicCombinatorics.coeff_embedUnivInBiv f n k

/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma eq_of_embed_univ_in_biv_eq
-- given
  {R : Type*} [CommSemiring R] (f g : ℕ → PowerSeries R)
  (h : AlgebraicCombinatorics.embedUnivInBiv f = AlgebraicCombinatorics.embedUnivInBiv g) :
-- imply
  f = g := by
-- proof
  apply AlgebraicCombinatorics.eq_of_embedUnivInBiv_eq f g h

/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma binomial_gen_fun_eq :
-- imply
  AlgebraicCombinatorics.binomialGenFun =
    AlgebraicCombinatorics.binomialGenFunClosedForm := by
-- proof
  apply AlgebraicCombinatorics.binomialGenFun_eq

/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma binomial_gen_fun_xyk_eq :
-- imply
  AlgebraicCombinatorics.embedUnivInBiv
    (fun k => (PowerSeries.X : PowerSeries ℚ) ^ k * (1 - PowerSeries.X)⁻¹ ^ (k + 1)) =
    AlgebraicCombinatorics.embedUnivInBiv
      (fun k => PowerSeries.mk (fun n => (n.choose k : ℚ))) := by
-- proof
  apply AlgebraicCombinatorics.binomialGenFun_xyk_eq

/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma sum_choose_pow_eq
-- given
  (k : ℕ) :
-- imply
  (PowerSeries.X : PowerSeries ℚ) ^ k * (1 - PowerSeries.X)⁻¹ ^ (k + 1) =
    PowerSeries.mk (fun n => (n.choose k : ℚ)) := by
-- proof
  apply AlgebraicCombinatorics.sum_choose_pow_eq k

/--
[Multivariate](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/FPS/Multivariate.lean)
-/
@[path]
private lemma partial_deriv_mul_eq
-- given
  {R : Type*} [CommSemiring R] {σ : Type*} [DecidableEq σ] (i : σ) (f g : MvPowerSeries σ R) :
-- imply
  AlgebraicCombinatorics.partialDeriv i (f * g) =
    AlgebraicCombinatorics.partialDeriv i f * g +
      f * AlgebraicCombinatorics.partialDeriv i g := by
-- proof
  apply AlgebraicCombinatorics.partialDeriv_mul i f g


-- created on 2026-10-11
