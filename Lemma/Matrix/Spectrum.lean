import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.Matrix.Spectrum
open scoped ComplexOrder Matrix.Norms.L2Operator
open Matrix


/--
[IsHermitian.charpoly_isRealRooted](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Matrix/Spectrum.lean)
-/
@[path]
private lemma IsHermitian_charpoly_isRealRooted_eq
  [Fintype n] [DecidableEq n]
  {A : Matrix n n ℂ}
-- given
  (hA : A.IsHermitian) :
-- imply
  A.charpoly.IsRealRooted := by
-- proof
  apply Matrix.IsHermitian.charpoly_isRealRooted hA

/--
[PosSemidef.l2_opNorm_eq_maxRealRoot_charpoly](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Matrix/Spectrum.lean)
-/
@[path]
private lemma PosSemidef_l2_opNorm_eq_maxRealRoot_charpoly_eq
  [Fintype n] [DecidableEq n] [Nonempty n]
  {A : Matrix n n ℂ}
-- given
  (hA : A.PosSemidef) :
-- imply
  ‖A‖ = A.charpoly.maxRealRoot := by
-- proof
  apply Matrix.PosSemidef.l2_opNorm_eq_maxRealRoot_charpoly hA


-- created on 2026-10-20
