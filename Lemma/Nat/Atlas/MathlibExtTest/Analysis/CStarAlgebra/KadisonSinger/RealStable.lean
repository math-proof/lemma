import Mathlib
import sympy.Basic
import Theorem.MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable
open scoped ComplexOrder
open MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable

/--
[finOne_one_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean)
-/
@[path]
private lemma finOne_one_posSemidef :
  (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ).PosSemidef := by
  rw [show (!![(1 : ℂ)] : Matrix (Fin 1) (Fin 1) ℂ) =
    Matrix.diagonal (fun _ ↦ 1) by
    ext i j
    fin_cases i
    fin_cases j
    simp]
  exact Matrix.PosSemidef.diagonal (fun i ↦ by norm_num)

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable


-- created on 2026-10-23
