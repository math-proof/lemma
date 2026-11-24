module
public import Def.Analysis.CStarAlgebra.KadisonSinger.Barrier
public import Theorem.Real.CStarAlgebra.KadisonSinger.Barrier
open scoped BigOperators ComplexOrder
open MvPolynomial
open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/Barrier.lean -/
namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Barrier

-- The barrier bound applies to the one-dimensional identity covariance matrix.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).maxRealRoot ≤
        (1 + Real.sqrt 1) ^ 2 := by
  apply mixedCharacteristicPolynomial_maxRealRoot_le
  · norm_num
  · intro i
    exact finOne_one_posSemidef
  · ext i j
    fin_cases i
    fin_cases j
    simp
  · intro i
    simp [Matrix.trace]

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.Barrier
