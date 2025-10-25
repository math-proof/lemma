import Lemma.Nat.Gt_0.of.Gt_0.Gt_0
import Lemma.Int.Gt_0.of.Lt_0.Lt_0
import Lemma.Nat.Le.of.Eq
import Lemma.Bool.Or.is.NotAndNotS
import Lemma.Bool.NotAnd.is.Imp_Not
import Lemma.Nat.NotLe.is.Gt
import Lemma.Nat.NotLt.of.Ge
import Lemma.Nat.Lt.ou.Eq.ou.Gt
import Lemma.Nat.NotGt.of.Lt
import Lemma.Nat.Ge.of.Gt
import Lemma.Nat.Le.of.Lt
open Bool Nat Int


@[main]
private lemma main
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
  refine Or.of.NotAndNotS ?_
  simp only [NotAnd.is.Imp_Not, NotLe.is.Gt]
  intro h_ab h_!ab
  apply NotLt.of.Ge h
  rcases Lt.ou.Eq.ou.Gt 0 a with ha | ha | ha
  ·
    have := Ge.of.Gt ha
    have := h_!ab this
    exact Gt_0.of.Gt_0.Gt_0 ha this
  ·
    have ha := ha.symm
    have h_Le_0 := Le.of.Eq ha
    have h₀ := h_ab h_Le_0
    have h₀ := NotGt.of.Lt h₀
    grind
  ·
    have := Le.of.Lt ha
    have := h_ab this
    exact Gt_0.of.Lt_0.Lt_0 ha this


-- created on 2025-03-29
-- updated on 2025-10-25
