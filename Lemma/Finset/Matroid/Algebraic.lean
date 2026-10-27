import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Matroid.Algebraic.Part2
open Matroid


namespace Matroid

/--
[AlgebraicRepresentation.toIsAlgebraicOver](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean)
-/
@[path]
lemma AlgebraicRepresentation.toIsAlgebraicOver
  {K : Type u} [Field K]
  {E : Type v}
  {M : Matroid E}
  {self : AlgebraicRepresentation.{u, v, max u v} K M} :
-- imply
  IsAlgebraicOver K M :=
-- proof
  ⟨self⟩

end Matroid

namespace Matroid

/--
[AlgebraicRepresentationSomeField.toIsAlgebraic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Matroid/Algebraic.lean)
-/
@[path]
lemma AlgebraicRepresentationSomeField.toIsAlgebraic
  {E : Type v}
  {M : Matroid E}
  {self : AlgebraicRepresentationSomeField M} :
-- imply
  IsAlgebraic M :=
-- proof
  ⟨self⟩

end Matroid


-- created on 2026-10-20
-- updated on 2026-10-26
