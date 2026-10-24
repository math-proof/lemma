import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving
open scoped BigOperators ComplexOrder Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[unitFrame_sum](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma unitFrame_sum :
  ∑ i, Matrix.vecMulVec (unitFrame i) (star (unitFrame i)) =
    (1 : Matrix (Fin 1) (Fin 1) ℂ) := by
  ext i j
  fin_cases i
  fin_cases j
  simp [unitFrame, Matrix.vecMulVec_apply, Pi.star_apply]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[unitFrame_norm](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma unitFrame_norm (i : Fin 1) :
  ∑ k, ‖unitFrame i k‖ ^ 2 ≤ (1 : ℝ) := by
  simp [unitFrame]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[pauliX_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[pauliX_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma pauliX_diagonal (i : Fin 2) : pauliX i i = 0 := by
  fin_cases i <;> rfl

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[pauliX_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving

/--
[pauliX_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Paving.lean)
-/
@[path]
private lemma pauliX_norm_le_one : ‖pauliX‖ ≤ 1 := by
  have hstar : star pauliX = pauliX := pauliX_isHermitian
  have hsquare : ‖pauliX‖ * ‖pauliX‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hstar, pauliX_mul_self, norm_one]
  nlinarith [norm_nonneg pauliX]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Paving


-- created on 2026-10-23
