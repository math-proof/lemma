import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.HZeroBasis
open MetaMathlibExt.MultipleZeta
open MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted


/--
[hZero_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HZeroBasis.lean)
-/
@[path]
private lemma hZero_basis_eq
  :
-- imply
  ∃ b : Module.Basis HZeroIndex ℚ ↥hZero,
    ∀ idx : HZeroIndex, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx.val := by
-- proof
  apply MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted.hZero_basis


-- created on 2026-10-20
