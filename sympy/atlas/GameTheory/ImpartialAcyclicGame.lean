/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GameTheory/ImpartialAcyclicGame.lean -/

import Mathlib.Data.Set.Defs
import Batteries.Tactic.Init

namespace MetaMathlibExt

/-! # P- and N-positions of impartial acyclic games
-/

/--
The set of P-positions of a terminating impartial game is uniquely determined by stability
and absorption. N-positions are represented by the complement of the P-positions.

Source: Antoine Renard and Michel Rigo, "Variants of Wythoff Game with Terminal
Positions or Blocking Maneuvers," Journal of Integer Sequences 29 (2026),
Article 26.1.6, Proposition (Folklore) (label pro:kernel), lines 438–448,
https://cs.uwaterloo.ca/journals/JIS/VOL29/Rigo/rigo5.tex; stability and
absorption are defined in lines 430–436. Termination is encoded by the
well-foundedness of the move relation on the acyclic game graph.
Proves `Wanted` entry `pPositions_unique`.
-/
theorem pPositions_unique
    {Position : Type*}
    (move : Position → Position → Prop)
    (hmove : WellFounded (fun next current => move current next))
    (P Q : Set Position)
    (hP_stable : ∀ x y : Position, x ∈ P → move x y → y ∉ P)
    (hP_absorbing : ∀ x : Position, x ∉ P → ∃ y : Position, move x y ∧ y ∈ P)
    (hQ_stable : ∀ x y : Position, x ∈ Q → move x y → y ∉ Q)
    (hQ_absorbing : ∀ x : Position, x ∉ Q → ∃ y : Position, move x y ∧ y ∈ Q) :
    P = Q := by
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
