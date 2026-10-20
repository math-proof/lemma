import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.DirichletCharacter.QuadraticDirichletCharacter
open MetaMathlibExt


/--
[quadraticDirichletCharacter](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/DirichletCharacter/QuadraticDirichletCharacter.lean)
-/
@[path]
private lemma quadraticDirichletCharacter_eq
  {D : ℤ}
-- given
  (hD : IsFundamentalDiscriminant D) :
-- imply
  ∃! χ : DirichletCharacter ℤ D.natAbs,
    ∀ n : ℕ, χ (n : ZMod D.natAbs) = kroneckerSym D n := by
-- proof
  apply MetaMathlibExt.quadraticDirichletCharacter D hD


-- created on 2026-10-20
