import Mathlib
import sympy.Basic
import sympy.atlas.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger
open scoped Matrix.Norms.L2Operator
open MathlibExt.Analysis.CStarAlgebra.KadisonSingerWanted


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

/--
[pauliX_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma pauliX_isHermitian : pauliX.IsHermitian := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

/--
[pauliX_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma pauliX_diagonal (i : Fin 2) : pauliX i i = 0 := by
  fin_cases i <;> rfl

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

/--
[pauliX_mul_self](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma pauliX_mul_self : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger

/--
[pauliX_norm_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger.lean)
-/
@[path]
private lemma pauliX_norm_le_one : ‖pauliX‖ ≤ 1 := by
  have hstar : star pauliX = pauliX := pauliX_isHermitian
  have hsquare : ‖pauliX‖ * ‖pauliX‖ = 1 := by
    rw [← CStarRing.norm_star_mul_self, hstar, pauliX_mul_self, norm_one]
  nlinarith [norm_nonneg pauliX]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger


-- created on 2026-10-23
