/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Matrix/Spectrum.lean -/

import Lemma.Matrix.Spectrum

open scoped ComplexOrder Matrix.Norms.L2Operator

namespace MathlibExtTest.Analysis.Matrix.Spectrum

private def positiveDiagonal : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.diagonal ![(1 : ℂ), 2]

-- A nonconstant positive diagonal matrix has a real-rooted characteristic polynomial.
example : positiveDiagonal.charpoly.IsRealRooted :=
  Matrix.IsHermitian.charpoly_isRealRooted positiveDiagonal_isHermitian

-- Its L2 operator norm equals the largest root of its characteristic polynomial.
example : ‖positiveDiagonal‖ = positiveDiagonal.charpoly.maxRealRoot :=
  Matrix.PosSemidef.l2_opNorm_eq_maxRealRoot_charpoly positiveDiagonal_posSemidef

end MathlibExtTest.Analysis.Matrix.Spectrum
