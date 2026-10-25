/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/CStarAlgebra/KadisonSinger/RealStable.lean -/

import Def.Analysis.CStarAlgebra.KadisonSinger.RealStable
import Lemma.Real.CStarAlgebra.KadisonSinger.RealStable
open scoped ComplexOrder

open MvPolynomial

open MathlibExt.Analysis.CStarAlgebra.KadisonSinger


namespace MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable

-- The determinant polynomial of a positive one-dimensional matrix is stable.
example :
    (mixedDetPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsStable := by
  apply mixedDetPolynomial_isStable_of_posSemidef
  intro i
  exact finOne_one_posSemidef

-- The same concrete determinant polynomial is real stable.
example :
    (mixedDetPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsRealStable := by
  apply mixedDetPolynomial_isRealStable_of_posSemidef
  intro i
  exact finOne_one_posSemidef

-- A concrete mixed characteristic polynomial is monic.
example :
    (mixedCharacteristicPolynomial (fun _ : Fin 1 ↦ !![(1 : ℂ)])).Monic :=
  mixedCharacteristicPolynomial_monic _

-- Its degree is the dimension of the one-dimensional matrix space.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).natDegree = 1 := by
  simpa using mixedCharacteristicPolynomial_natDegree
    (fun _ : Fin 1 ↦ !![(1 : ℂ)])

-- Positive semidefiniteness makes the concrete mixed characteristic polynomial real-rooted.
example :
    (mixedCharacteristicPolynomial
      (fun _ : Fin 1 ↦ !![(1 : ℂ)])).IsRealRooted := by
  apply mixedCharacteristicPolynomial_isRealRooted_of_posSemidef
  intro i
  exact finOne_one_posSemidef

end MathlibExtTest.Analysis.CStarAlgebra.KadisonSinger.RealStable
