/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Matrix/Spectrum.lean -/
module

public import Theorem.Matrix.Spectrum
public import Def.MathlibExtTest.Analysis.Matrix.Spectrum
open scoped ComplexOrder Matrix.Norms.L2Operator

public section

namespace MathlibExtTest.Analysis.Matrix.Spectrum

-- A nonconstant positive diagonal matrix has a real-rooted characteristic polynomial.
example : positiveDiagonal.charpoly.IsRealRooted :=
  Matrix.IsHermitian.charpoly_isRealRooted positiveDiagonal_isHermitian

-- Its L2 operator norm equals the largest root of its characteristic polynomial.
example : ‖positiveDiagonal‖ = positiveDiagonal.charpoly.maxRealRoot :=
  Matrix.PosSemidef.l2_opNorm_eq_maxRealRoot_charpoly positiveDiagonal_posSemidef

end MathlibExtTest.Analysis.Matrix.Spectrum
