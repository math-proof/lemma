import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Matroid.Algebraic
open Matroid


/--
[AlgebraicRepresentation.toIsAlgebraicOver](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean)
-/
@[path]
private lemma AlgebraicRepresentation_toIsAlgebraicOver_eq
  {K : Type u} [Field K]
  {E : Type v}
  {M : Matroid E}
  {self : AlgebraicRepresentation.{u, v, max u v} K M} :
-- imply
  IsAlgebraicOver K M := by
-- proof
  apply Matroid.AlgebraicRepresentation.toIsAlgebraicOver self

/--
[AlgebraicRepresentationSomeField.toIsAlgebraic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean)
-/
@[path]
private lemma AlgebraicRepresentationSomeField_toIsAlgebraic_eq
  {E : Type v}
  {M : Matroid E}
  {self : AlgebraicRepresentationSomeField M} :
-- imply
  IsAlgebraic M := by
-- proof
  apply Matroid.AlgebraicRepresentationSomeField.toIsAlgebraic self


-- created on 2026-10-20
