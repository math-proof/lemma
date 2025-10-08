import Lemma.Vector.Card.eq.PowCard
import Lemma.Algebra.Eq.of.EqPowS.Gt_1
open Algebra Vector


@[main]
private lemma main
  [Fintype ι]
-- given
  (h₀ : Fintype.card ι > 1)
  (h₁ : List.Vector ι n = List.Vector ι m) :
-- imply
  n = m := by
-- proof
  have h_n := Card.eq.PowCard (ι := ι) n
  have h_m := Card.eq.PowCard (ι := ι) m
  have h_card : Fintype.card (List.Vector ι n) = Fintype.card (List.Vector ι m) := by simp_all
  have h_eq := h_n.symm.trans h_card |>.trans h_m
  apply Eq.of.EqPowS.Gt_1 h₀ h_eq


-- created on 2025-05-23
