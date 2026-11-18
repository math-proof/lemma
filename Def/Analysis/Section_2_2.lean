import Mathlib
import Abbrev.Analysis.Section_2_1
import Abbrev.Analysis.Section_2_1_api
import Instance.Analysis.Section_2_2
/-!
# Analysis I, Section 2.2: Addition

This file is a translation of Section 2.2 of Analysis I to Lean 4.  All numbering refers to the
original text.

I have attempted to make the translation as faithful a paraphrasing as possible of the original
text. When there is a choice between a more idiomatic Lean solution and a more faithful
translation, I have generally chosen the latter.  In particular, there will be places where the
Lean code could be "golfed" to be more elegant and idiomatic, but I have consciously avoided
doing so.

Main constructions and results of this section:

- Definition of addition and order for the "Chapter 2" natural numbers, {name}`Chapter2.Nat`.
- Establishment of basic properties of addition and order.

Note: at the end of this chapter, the {name}`Chapter2.Nat` class will be deprecated in favor of the
standard Mathlib class {name}`_root_.Nat`, or {lean}`ℕ`.  However, we will develop the properties of
{name}`Chapter2.Nat` "by hand" for pedagogical purposes.

## Tips from past users

Users of the companion who have completed the exercises in this section are welcome to send their
tips for future users in this section as PRs.

- (Add tip here)

-/


namespace Chapter2

/-- This illustration of the {tactic}`abel` tactic is not from the
    textbook. -/
def Nat.IsPos (n:Nat) : Prop := n ≠ 0

private theorem add_zero_for_decLe (n : Nat) : n + 0 = n := by
  revert n
  apply Nat.induction (fun n => n + 0 = n)
  · exact Nat.recurse_zero (fun _ sum ↦ sum++) 0
  · intro n ih
    calc
      (n++) + 0 = (n + 0)++ := Nat.recurse_succ (fun _ sum ↦ sum++) 0 n
      _ = n++ := by rw [ih]

private theorem add_succ_for_decLe (n m : Nat) : n + (m++) = (n + m)++ := by
  revert n
  apply Nat.induction (fun n => n + (m++) = (n + m)++)
  · calc
      0 + (m++) = m++ := Nat.recurse_zero (fun _ sum ↦ sum++) (m++)
      _ = (0 + m)++ := by rw [show 0 + m = m from Nat.recurse_zero (fun _ sum ↦ sum++) m]
  · intro n ih
    calc
      (n++) + (m++) = (n + (m++))++ := Nat.recurse_succ (fun _ sum ↦ sum++) (m++) n
      _ = ((n + m)++)++ := by rw [ih]
      _ = ((n++) + m)++ := by rw [show (n++) + m = (n + m)++ from Nat.recurse_succ (fun _ sum ↦ sum++) m n]

private theorem ne_succ_add_for_decLe (n k : Nat) : n ≠ (n + k)++ := by
  revert n
  apply Nat.induction (fun n => n ≠ (n + k)++)
  · intro h
    exact Nat.succ_ne (0 + k) h.symm
  · intro n ih h
    have hsucc : (n++) + k = (n + k)++ :=
      Nat.recurse_succ (fun _ sum ↦ sum++) k n
    exact ih (Nat.succ_cancel (h.trans (congrArg (fun t => t++) hsucc)))

/--
(Not from textbook) Establish the decidability of this order computably. The portion of the proof
involving decidability has been provided; the remaining claims about the natural numbers are
proved from the recursive definition of addition.

Compare with Mathlib's {name}`Nat.decLe`.

This is `Decidable (a ≤ b)` once `instance Nat.instLE` (`le n m := ∃ a, m = n + a`) is available.
The type is written in unfolded form so this file need not import that instance (which lives in
`Instance.Analysis.Section_2_2.Part2` and already imports this file).
-/
def Nat.decLe : (a b : Nat) → Decidable (∃ k : Nat, b = a + k)
  | 0, b => by
    apply isTrue
    exact ⟨b, (Nat.recurse_zero (fun _ sum ↦ sum++) b).symm⟩
  | a++, b => by
    cases decLe a b with
    | isTrue h =>
      cases decEq a b with
      | isTrue hab =>
        apply isFalse
        intro ⟨k, hk⟩
        have hsucc : (a++) + k = (a + k)++ :=
          Nat.recurse_succ (fun _ sum ↦ sum++) k a
        subst hab
        exact ne_succ_add_for_decLe a k (hk.trans hsucc)
      | isFalse hne =>
        apply isTrue
        obtain ⟨k, hk⟩ := h
        match k with
        | 0 =>
          exact (hne (hk.trans (add_zero_for_decLe a)).symm).elim
        | m++ =>
          refine ⟨m, ?_⟩
          have hsucc : (a++) + m = (a + m)++ :=
            Nat.recurse_succ (fun _ sum ↦ sum++) m a
          exact hk.trans ((add_succ_for_decLe a m).trans hsucc.symm)
    | isFalse h =>
      apply isFalse
      intro ⟨k, hk⟩
      have hsucc : (a++) + k = (a + k)++ :=
        Nat.recurse_succ (fun _ sum ↦ sum++) k a
      exact h ⟨k++, hk.trans (hsucc.trans (add_succ_for_decLe a k).symm)⟩

end Chapter2
