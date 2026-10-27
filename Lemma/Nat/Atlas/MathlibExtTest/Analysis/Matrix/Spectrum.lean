import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.MathlibExtTest.Analysis.Matrix.Spectrum
open scoped ComplexOrder Matrix.Norms.L2Operator


namespace MathlibExtTest.Analysis.Matrix.Spectrum

/--
[positiveDiagonal_isHermitian](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Matrix/Spectrum.lean)
-/
@[path]
private lemma positiveDiagonal_isHermitian : positiveDiagonal.IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  intro i
  fin_cases i <;> norm_num

end MathlibExtTest.Analysis.Matrix.Spectrum

namespace MathlibExtTest.Analysis.Matrix.Spectrum

/--
[positiveDiagonal_posSemidef](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Matrix/Spectrum.lean)
-/
@[path]
private lemma positiveDiagonal_posSemidef : positiveDiagonal.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  fin_cases i <;> norm_num

end MathlibExtTest.Analysis.Matrix.Spectrum


-- created on 2026-10-23
