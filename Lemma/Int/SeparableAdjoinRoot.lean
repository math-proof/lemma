import Mathlib
import sympy.Basic
import sympy.atlas.FieldTheory.SeparableAdjoinRoot
open scoped Polynomial
open IntermediateField
open Algebra


/--
[isSeparable_iff_exists_monic_irreducible_separable](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/FieldTheory/SeparableAdjoinRoot.lean)
-/
@[path]
private lemma isSeparable_iff_exists_monic_irreducible_separable_eq
  [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] :
-- imply
  Algebra.IsSeparable K L ↔
      ∃ f : K[X], f.Monic ∧ Irreducible f ∧ f.Separable ∧
        Nonempty (L ≃ₐ[K] AdjoinRoot f) := by
-- proof
  apply Algebra.isSeparable_iff_exists_monic_irreducible_separable K L


-- created on 2026-10-20
