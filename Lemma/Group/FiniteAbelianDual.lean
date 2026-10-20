import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.FiniteAbelianDual
open scoped DirectSum
open MathlibExt.GroupTheory.FiniteAbelianDualWanted


/--
[finite_abelian_dual_iso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean)
-/
@[path]
private lemma finite_abelian_dual_iso_eq
  [AddCommGroup α] [Finite α] :
-- imply
  Nonempty (α ≃+ AddChar α ℂ) := by
-- proof
  apply MathlibExt.GroupTheory.FiniteAbelianDualWanted.finite_abelian_dual_iso α

/--
[dual_prod](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/FiniteAbelianDual.lean)
-/
@[path]
private lemma dual_prod_eq
  [AddCommGroup α] [AddCommGroup β] :
-- imply
  Nonempty (AddChar (α × β) ℂ ≃+ (AddChar α ℂ × AddChar β ℂ)) := by
-- proof
  apply MathlibExt.GroupTheory.FiniteAbelianDualWanted.dual_prod α β


-- created on 2026-10-20
