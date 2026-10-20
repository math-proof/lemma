import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
open scoped BigOperators
open Polynomial
open MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


/--
[eval_mixedDetPolynomial](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma eval_mixedDetPolynomial_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {z : Unit ⊕ Fin m → ℂ} :
-- imply
  MvPolynomial.eval z (mixedDetPolynomial A) =
    Matrix.det (Matrix.scalar d (z (Sum.inl ())) + ∑ i, z (Sum.inr i) • A i) := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.eval_mixedDetPolynomial A z

/--
[mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {u v : d → ℂ}
-- given
  (hi : A i = Matrix.vecMulVec u v) :
-- imply
  pderiv (Sum.inr i) (pderiv (Sum.inr i) (mixedDetPolynomial A)) = 0 := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec A i u v hi

/--
[mixedCharacteristicPolynomial_update_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_update_sum_eq
  [Fintype d] [DecidableEq d] [Fintype ι]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {w : ι → ℝ}
  {C : ι → Matrix d d ℂ}
-- given
  (hsum : ∑ a, w a = 1) :
-- imply
  mixedCharacteristicPolynomial (Function.update A i (∑ a, (w a : ℂ) • C a)) =
    ∑ a, (w a : ℂ) • mixedCharacteristicPolynomial (Function.update A i (C a)) := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_update_sum A i w C hsum

/--
[mixedCharacteristicPolynomial_update_affine](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_update_affine_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {i : Fin m}
  {B C : Matrix d d ℂ}
  {t : ℝ} :
-- imply
  mixedCharacteristicPolynomial
    (Function.update A i ((1 - (t : ℂ)) • B + (t : ℂ) • C)) =
    (1 - (t : ℂ)) • mixedCharacteristicPolynomial (Function.update A i B) +
    (t : ℂ) • mixedCharacteristicPolynomial (Function.update A i C) := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_update_affine A i B C t

/--
[mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec_eq
  [Fintype d] [DecidableEq d]
  {m : ℕ}
  {A : Fin m → Matrix d d ℂ}
  {u v : Fin m → d → ℂ}
-- given
  (hA : ∀ i, A i = Matrix.vecMulVec (u i) (v i)) :
-- imply
  mixedCharacteristicPolynomial A = Matrix.charpoly (∑ i, A i) := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec A u v hA

/--
[mixedCharacteristicPolynomial_fin_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean)
-/
@[path]
private lemma mixedCharacteristicPolynomial_fin_one_eq
  {a : ℂ} :
-- imply
  mixedCharacteristicPolynomial (m := by
-- proof
  apply MathlibExt.Analysis.CStarAlgebra.KadisonSinger.mixedCharacteristicPolynomial_fin_one a


-- created on 2026-10-20
