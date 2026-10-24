/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/MSS.lean -/

import sympy.atlas.Analysis.CStarAlgebra.KadisonSinger.MSS
import Lemma.Real.CStarAlgebra.KadisonSinger.MSS

open scoped BigOperators Matrix.Norms.L2Operator

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS

noncomputable section

universe u

-- The proved MSS bound is available at every matrix-index universe.
example : FiniteMSSBound.{u} := finiteMSSBound

private def supportSize : Fin 1 → ℕ := fun _ ↦ 2

private def probability : (i : Fin 1) → Fin (supportSize i) → ℝ :=
  fun _ ↦ ![1 / 2, 1 / 2]

private def randomVector : (i : Fin 1) → Fin (supportSize i) → Fin 1 → ℂ :=
  fun _ ↦ ![![1], ![-1]]

-- Interlacing selects one outcome from a concrete symmetric two-point distribution.
example :
    ∃ ω : (i : Fin 1) → Fin (supportSize i),
      (Matrix.charpoly
        (∑ i, Matrix.vecMulVec (randomVector i (ω i))
          (star (randomVector i (ω i))))).maxRealRoot ≤
      (mixedCharacteristicPolynomial (fun i ↦
        ∑ a, probability i a •
          Matrix.vecMulVec (randomVector i a) (star (randomVector i a)))).maxRealRoot := by
  apply exists_outcome_maxRealRoot_le_mixedCharacteristicPolynomial
  · intro i
    norm_num [supportSize]
  · intro i a
    fin_cases i
    fin_cases a <;> change 0 ≤ (1 / 2 : ℝ) <;> norm_num
  · intro i
    fin_cases i
    change ∑ a : Fin 2, ![(1 / 2 : ℝ), 1 / 2] a = 1
    rw [Fin.sum_univ_two]
    change (1 / 2 : ℝ) + 1 / 2 = 1
    norm_num

-- The finite MSS bound controls the sole outcome of a one-point distribution.
example :
    ∃ ω : Fin 1 → Fin 1,
      ‖∑ i, Matrix.vecMulVec
        ((![![![1]]] : Fin 1 → Fin 1 → Fin 1 → ℂ) i (ω i))
        (star ((![![![1]]] : Fin 1 → Fin 1 → Fin 1 → ℂ) i (ω i)))‖ ≤
        (1 + Real.sqrt 1) ^ 2 := by
  apply finiteMSSBound (m := 1) (d := Fin 1) (s := fun _ ↦ 1)
    (p := ![![1]]) (v := ![![![1]]]) (η := 1)
  · intro i
    norm_num
  · norm_num
  · intro i a
    fin_cases i
    fin_cases a
    norm_num
  · intro i
    fin_cases i
    simp
  · have hv : (![1] : Fin 1 → ℂ) = fun _ ↦ 1 := by
      funext k
      fin_cases k
      rfl
    ext i j
    fin_cases i
    fin_cases j
    simp [hv, Matrix.vecMulVec_apply, Pi.star_apply]
  · intro i
    fin_cases i
    simp

end

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.MSS
