import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.MultipleZeta.HOneBasis
open `x`-run (which never occurs for `H^1` words). -/
open MetaMathlibExt.MultipleZeta
open MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted


/--
[hOne_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/MultipleZeta/HOneBasis.lean)
-/
@[path]
private lemma hOne_basis_eq
  :
-- imply
  ∃ b : Module.Basis Index ℚ ↥hOne,
    ∀ idx : Index, (↑(b idx) : FreeAlgebra ℚ Bool) = zMonomial idx := by
-- proof
  apply MathlibExt.NumberTheory.MultipleZeta.WordAlgebraWanted.hOne_basis


-- created on 2026-10-20
