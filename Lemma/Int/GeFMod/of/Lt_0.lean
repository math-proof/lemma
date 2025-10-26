import Lemma.Int.NegSucc.eq.NegAdd_1
import Lemma.Nat.SubNatNat.eq.Sub
import Lemma.Int.LeNeg.of.Ge_Neg
import Lemma.Int.LeNegS.of.Ge
import Lemma.Nat.LtMod.of.Gt_0
import Lemma.Nat.Ge.of.Gt
import Lemma.Int.NegSub.eq.Add_Neg
import Lemma.Nat.GeAddS.is.Ge
open Nat Int


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
