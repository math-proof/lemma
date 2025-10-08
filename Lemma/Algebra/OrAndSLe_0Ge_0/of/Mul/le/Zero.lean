import Lemma.Algebra.Gt_0.of.Gt_0.Gt_0
import Lemma.Algebra.Gt_0.of.Lt_0.Lt_0
import Lemma.Algebra.Le.of.Eq
import Lemma.Algebra.Ge.of.Eq
import Lemma.Bool.Or.is.NotAndNotS
import Lemma.Bool.NotAnd.is.Imp_Not
import Lemma.Algebra.NotLe.is.Gt
import Lemma.Algebra.NotLt.of.Ge
import Lemma.Algebra.Lt.ou.Eq.ou.Gt
import Lemma.Algebra.NotGt.of.Lt
import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.Le.of.Lt
open Algebra Bool Nat


@[main]
private lemma Main
  [Semiring α]
  [LinearOrder α]
  [ExistsAddOfLE α]
  [PosMulStrictMono α]
  [MulPosStrictMono α]
  [AddRightStrictMono α]
  [AddRightReflectLT α]
  {a b : α}
-- given
  (h : a * b ≤ 0) :
-- imply
  a ≤ 0 ∧ b ≥ 0 ∨ b ≤ 0 ∧ a ≥ 0 := by
-- proof
  rw [And.comm (a := b ≤ 0)]
  -- constructing the proof term with holes, splitting the main goal into subgoals.
  refine Or.of.NotAndNotS ?_
  simp only [NotAnd.is.Imp_Not, NotLe.is.Gt]
  intro ab nab
  apply NotLt.of.Ge h
  rcases Lt.ou.Eq.ou.Gt 0 a with ha | ha | ha
  ·
    have := Ge.of.Gt ha
    have := nab this
    exact Gt_0.of.Gt_0.Gt_0 ha this
  ·
    have ha := ha.symm
    rw [ha]
    have h_Ge_0 := Ge.of.Eq ha
    have h_Le_0 := Le.of.Eq ha
    have h₀ := ab h_Le_0
    have h₀ := NotGt.of.Lt h₀
    have h₁ := nab h_Ge_0
    have := h₀ h₁
    contradiction
  ·
    have := Le.of.Lt ha
    have := ab this
    exact Gt_0.of.Lt_0.Lt_0 ha this


-- created on 2025-03-29
-- updated on 2025-03-30
