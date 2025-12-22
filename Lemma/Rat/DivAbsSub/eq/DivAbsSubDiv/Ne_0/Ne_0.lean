import Lemma.Int.EqAbs_0.is.Eq_0
import Lemma.Int.MulSubS.eq.SubAddSMulS
import Lemma.Nat.AddAdd
import Lemma.Rat.AbsDiv.eq.DivAbsS
import Lemma.Rat.Div.eq.DivDivS.of.Ne_0
import Lemma.Rat.Div.eq.One.of.Ne_0
import Lemma.Rat.DivAdd.eq.AddDivS
import Lemma.Rat.DivMulS.eq.Div.of.Ne_0
import Lemma.Rat.DivSub.eq.SubDivS
import Lemma.Rat.MulDivS.eq.One.of.Ne_0.Ne_0
open Int Nat Rat


@[main]
private lemma main
  [Field α] [LinearOrder α] [IsStrictOrderedRing α]
  {a b : α}
-- given
  (h_b : b ≠ 0) :
-- imply
  |a - b| / (|a| + |b| + 1) = |a / b - 1| / (|a / b| + |b|⁻¹ + 1) := by
-- proof
  have h_b_abs_ne_0 := NeAbs_0.of.Ne_0 h_b
  rw [Div.eq.DivDivS.of.Ne_0 h_b_abs_ne_0]
  rw [AddAdd.comm]
  repeat rw [DivAdd.eq.AddDivS]
  repeat rw [DivAbsS.eq.AbsDiv]
  rw [DivSub.eq.SubDivS]
  repeat rw [Div.eq.One.of.Ne_0 (by assumption)]
  simp


-- created on 2025-12-22
