/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/MixedCharPoly.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
import Lemma.Real.CStarAlgebra.KadisonSinger.MixedCharPoly
open scoped BigOperators

open Matrix MvPolynomial

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly

-- Evaluating a concrete determinant polynomial substitutes its scalar variables.
example (z : Unit ⊕ Fin 1 → ℂ) :
    eval z
        (mixedDetPolynomial
          (fun _ : Fin 1 ↦ !![(2 : ℂ)])) =
      det (Matrix.scalar (Fin 1) (z (Sum.inl ())) +
        ∑ i, z (Sum.inr i) • !![(2 : ℂ)]) :=
  eval_mixedDetPolynomial _ z

-- A rank-one matrix coordinate makes the determinant polynomial multi-affine there.
example :
    pderiv (Sum.inr 0)
        (pderiv (Sum.inr 0)
          (mixedDetPolynomial
            (fun _ : Fin 1 ↦ vecMulVec ![(2 : ℂ)] ![(3 : ℂ)]))) = 0 :=
  mixedDetPolynomial_pderiv_sq_eq_zero_of_eq_vecMulVec
      (fun _ : Fin 1 ↦ vecMulVec ![(2 : ℂ)] ![(3 : ℂ)]) 0
      ![(2 : ℂ)] ![(3 : ℂ)] rfl

-- A nontrivial two-point convex average is affine in one matrix coordinate.
example :
    let A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ ↦ !![0]
    let w : Fin 2 → ℝ := ![1 / 4, 3 / 4]
    let C : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := ![!![1], !![2]]
    mixedCharacteristicPolynomial
        (Function.update A 0 (∑ a, (w a : ℂ) • C a)) =
      ∑ a, (w a : ℂ) •
        mixedCharacteristicPolynomial
          (Function.update A 0 (C a)) := by
  dsimp only
  exact mixedCharacteristicPolynomial_update_sum
    (fun _ : Fin 1 ↦ !![0]) 0 ![1 / 4, 3 / 4] ![!![1], !![2]] (by norm_num)

-- Binary affine dependence holds at a genuinely interior weight.
example :
    let A : Fin 1 → Matrix (Fin 1) (Fin 1) ℂ := fun _ ↦ !![0]
    mixedCharacteristicPolynomial
        (Function.update A 0
          ((1 - ((1 / 3 : ℝ) : ℂ)) • !![1] + ((1 / 3 : ℝ) : ℂ) • !![2])) =
      (1 - ((1 / 3 : ℝ) : ℂ)) •
          mixedCharacteristicPolynomial
            (Function.update A 0 !![1]) +
        ((1 / 3 : ℝ) : ℂ) •
          mixedCharacteristicPolynomial
            (Function.update A 0 !![2]) := by
  dsimp only
  exact mixedCharacteristicPolynomial_update_affine (fun _ : Fin 1 ↦ !![0]) 0
      !![1] !![2] (1 / 3)

-- Two concrete rank-one inputs recover the characteristic polynomial of their sum.
example :
    let u : Fin 2 → Fin 1 → ℂ := ![![1], ![2]]
    let v : Fin 2 → Fin 1 → ℂ := ![![3], ![4]]
    let A : Fin 2 → Matrix (Fin 1) (Fin 1) ℂ := fun i ↦ vecMulVec (u i) (v i)
    mixedCharacteristicPolynomial A =
      Matrix.charpoly (∑ i, A i) := by
  dsimp only
  exact mixedCharacteristicPolynomial_eq_charpoly_sum_of_eq_vecMulVec _ _ _
    (fun _ ↦ rfl)

-- The one-dimensional mixed characteristic polynomial has the expected linear form.
example :
    mixedCharacteristicPolynomial
        (m := 1) (d := Fin 1) (fun _ ↦ !![(2 : ℂ)]) =
      Polynomial.X - Polynomial.C 2 :=
  mixedCharacteristicPolynomial_fin_one 2

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MixedCharPoly
