import Lemma.Bool.IffEqS.of.Eq
import Lemma.List.LengthPermute.eq.Length
import Lemma.List.LengthSwap.eq.Length
import Lemma.List.GetSwap.eq.Ite.of.Lt_Length.Lt_Length.Lt
import Lemma.List.GetPermute__Neg.eq.Ite.of.Lt_Length
import Lemma.List.GetPermute.eq.Ite.of.Lt_Length.Lt_Length
import Lemma.Algebra.CoeSub.eq.SubCoeS.of.Ge
import Lemma.Algebra.ValSub.eq.SubValS.of.Gt
import Lemma.Algebra.Sub.ge.One.of.Lt
import Lemma.Algebra.LtValS.of.Lt
import Lemma.Algebra.EqSub_Sub.of.Gt
import Lemma.Algebra.Sub.ge.One.of.Gt
import Lemma.Nat.Le.of.Lt
import Lemma.Algebra.SubAdd.eq.Add_Sub.of.Ge
import Lemma.Algebra.LtSub.of.Lt
import Lemma.Algebra.Eq_0.of.Eq_Sub_1
import Lemma.Algebra.Ge_Sub_1
import Lemma.Algebra.EqAdd_Sub.of.Gt
import Lemma.List.GetElem.eq.None.of.Ge_Length
import Lemma.Algebra.GeSub_1.of.Gt
import Lemma.Algebra.Le.of.LtSub_1
import Lemma.Algebra.LeSub.is.Le_Add
import Lemma.Nat.Eq.of.Le.Le
import Lemma.Algebra.Gt.of.Ge.Gt
import Lemma.Algebra.Le.of.LeSubS.Le
import Lemma.Algebra.Lt.of.Lt.Lt
import Lemma.Algebra.Gt.of.Gt.Ge
import Lemma.Algebra.Le.of.Le_Sub
import Lemma.Algebra.Gt.is.Ge.Ne
import Lemma.Algebra.Ge_1.of.Gt
import Lemma.Nat.EqAddSub.of.Ge
import Lemma.Algebra.Eq.of.EqSubS.Ge.Ge
open Bool List Algebra Nat


@[main]
private lemma main
  {s : List α}
-- given
  (h_j : j < s.length)
  (h_ij : i < j) :
-- imply
  (s.permute ⟨i, by linarith⟩ (j - i)).permute ⟨j, by simp_all [LengthPermute.eq.Length]⟩ (i - j) = s := by
-- proof
  sorry

-- created on 2025-10-12
