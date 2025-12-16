import Lemma.Int.FMod.eq.Sub_MulFDiv
import Lemma.Int.SubAdd.eq.Add_Sub
import Lemma.Nat.Add
import Lemma.Int.Sub.eq.Add_Neg
import Lemma.Nat.EqAddS.is.Eq
import Lemma.Int.FDiv.eq.FloorDiv
import Lemma.Int.CoeAdd.eq.AddCoeS
import Lemma.Rat.DivAdd.eq.Add1Div.of.Ne_0
import Lemma.Int.NeCoeS.of.Ne
import Lemma.Rat.FloorAdd1.eq.Add1Floor
import Lemma.Nat.MulAdd.eq.AddMulS
open Int Nat Rat


@[main]
private lemma main
  {n d : ℤ} :
-- imply
  (d + n).fmod d = n.fmod d := by
-- proof
  if h : d = 0 then
    rw [h]
    norm_num
  else
    rw [FMod.eq.Sub_MulFDiv]
    rw [FMod.eq.Sub_MulFDiv]
    rw [Add.comm]
    rw [SubAdd.eq.Add_Sub]
    rw [Sub.eq.Add_Neg (a := n)]
    apply EqAddS.of.Eq.left
    repeat rw [FDiv.eq.FloorDiv (α := ℚ)]
    rw [CoeAdd.eq.AddCoeS]
    rw [Add.comm]
    have h := NeCoeS.of.Ne (R := ℚ) h
    rw [DivAdd.eq.Add1Div.of.Ne_0 h]
    rw [FloorAdd1.eq.Add1Floor]
    rw [MulAdd.eq.AddMulS]
    norm_num


-- created on 2025-03-29
-- updated on 2025-04-26
