import Mathlib
import sympy.Basic
import Abbrev.v1.Atlas.TensorCategories.code.Proposition_1_6_4
open CategoryTheory MonoidalCategory


/--
[Proposition_1_6_4](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_6_4.lean)
-/
@[path]
private lemma Proposition_1_6_4_eq
  {k : Type*}
  [Field k]
  {A : Type*}
  [Ring A]
  [Algebra k A]
  [Module.Finite k A] :
-- imply
  ∃ (_ : MonoidalCategory (ModuleCat (Prop164.EnvelopingAlgebra k A))), Nonempty (Prop164.bimod_endRightExact_equiv k A).functor.Monoidal := by
-- proof
  apply Proposition_1_6_4 k A


-- created on 2026-10-23
