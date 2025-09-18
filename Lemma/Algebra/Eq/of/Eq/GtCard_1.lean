import Lemma.Algebra.Card.eq.PowCard
import Lemma.Algebra.Eq.of.EqPowS.Gt_1
open Algebra


@[main]
private lemma main
  [Fintype α]
-- given
  (h₀ : Fintype.card α > 1)
  (h₁ : List.Vector α n = List.Vector α m) :
-- imply
  n = m := by
-- proof
  have h_n := Card.eq.PowCard (α := α) n
  have h_m := Card.eq.PowCard (α := α) m
  have h_card : Fintype.card (List.Vector α n) = Fintype.card (List.Vector α m) := by simp_all
  have h_eq := h_n.symm.trans h_card |>.trans h_m
  apply Eq.of.EqPowS.Gt_1 h₀ h_eq


-- created on 2025-05-23
