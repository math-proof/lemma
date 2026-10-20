import Mathlib
import sympy.Basic
import sympy.atlas.GameTheory.ImpartialAcyclicGame
open MetaMathlibExt


/--
[pPositions_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ImpartialAcyclicGame.lean)
-/
@[path]
private lemma pPositions_unique_eq
  {P Q : Set Position}
-- given
  (move : Position → Position → Prop)
  (hmove : WellFounded (fun next current => move current next))
  (hP_stable : ∀ x y : Position, x ∈ P → move x y → y ∉ P)
  (hP_absorbing : ∀ x : Position, x ∉ P → ∃ y : Position, move x y ∧ y ∈ P)
  (hQ_stable : ∀ x y : Position, x ∈ Q → move x y → y ∉ Q)
  (hQ_absorbing : ∀ x : Position, x ∉ Q → ∃ y : Position, move x y ∧ y ∈ Q) :
-- imply
  P = Q := by
-- proof
  apply MetaMathlibExt.pPositions_unique move hmove P Q hP_stable hP_absorbing hQ_stable hQ_absorbing


-- created on 2026-10-20
