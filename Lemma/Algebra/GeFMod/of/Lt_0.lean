import Lemma.Algebra.NegSucc.eq.NegAdd_1
import Lemma.Algebra.SubNatNat.eq.Sub
import Lemma.Algebra.LeNeg.of.Ge_Neg
import Lemma.Algebra.LeNegS.of.Ge
import Lemma.Algebra.LtMod.of.Gt_0
import Lemma.Nat.Ge.of.Gt
import Lemma.Algebra.NegSub.eq.Add_Neg
import Lemma.Algebra.GeAddS.is.Ge
open Algebra Nat


@[main]
private lemma main
  {n d : ℤ}
-- given
  (h : d < 0) :
-- imply
  n.fmod d ≥ d := by
-- proof
  unfold Int.fmod
  match h_n : n, h_d : d with
  | 0, d =>
    simp
    linarith
  | .ofNat n, .ofNat d =>
    contradiction
  | .ofNat (.succ n'), .negSucc d' =>
    simp_all
    rw [NegSucc.eq.NegAdd_1]
    rw [SubNatNat.eq.Sub]
    apply LeNeg.of.Ge_Neg
    rw [NegSub.eq.Add_Neg]
    apply GeAddS.of.Ge.left
    linarith
  | .negSucc n', .ofNat d =>
    contradiction
  | .negSucc n', .negSucc d' =>
    simp_all
    rw [NegSucc.eq.NegAdd_1]
    apply LeNegS.of.Ge
    apply Ge.of.Gt
    apply LtMod.of.Gt_0
    linarith


-- created on 2025-03-28
-- updated on 2025-03-29
