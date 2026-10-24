import Mathlib
import sympy.Basic
import Batteries.Tactic.Init


namespace MetaMathlibExt

/--
[pPositions_unique](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ImpartialAcyclicGame.lean)
-/
@[path]
lemma pPositions_unique
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
  have key : ∀ x : Position, (x ∈ P ↔ x ∈ Q) :=
    fun x => hmove.induction (C := fun x => (x ∈ P ↔ x ∈ Q)) x
      (fun x ih => (⟨fun hxP => by
        by_contra hxQ
        obtain ⟨y, hxy, hyQ⟩ := hQ_absorbing x hxQ
        exact hP_stable x y hxP hxy ((ih y hxy).mpr hyQ),
        fun hxQ => by
        by_contra hxP
        obtain ⟨y, hxy, hyP⟩ := hP_absorbing x hxP
        exact hQ_stable x y hxQ hxy ((ih y hxy).mp hyP)⟩ : (x ∈ P ↔ x ∈ Q)))
  exact Set.ext key

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
