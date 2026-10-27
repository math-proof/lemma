import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraNotes.code.Ideals
open Ideals


namespace Ideals

/--
[isMaximal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Ideals.lean)
-/
@[path]
lemma isMaximal_iff
  {R : Type*}
  [CommRing R]
  {I : Ideal R} :
-- imply
  I.IsMaximal ↔ (I ≠ ⊤ ∧ ∀ J : Ideal R, I ≤ J → J = I ∨ J = ⊤) := by
-- proof
  constructor
  · intro hI
    refine ⟨hI.ne_top, fun J hIJ => ?_⟩
    obtain h | h := hIJ.eq_or_lt
    · left; exact h.symm
    · right; exact hI.out.2 J h
  · intro ⟨hne, honly⟩
    constructor
    refine ⟨hne, fun J hIJ => ?_⟩
    obtain h | h := honly J (le_of_lt hIJ)
    · exact absurd hIJ (h ▸ lt_irrefl I)
    · exact h

end Ideals


-- created on 2026-10-23
