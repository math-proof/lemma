import Lemma.Bool.SEq.is.Eq
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetGetSlice.eq.Get_Add.of.GtSubMin
import Lemma.Tensor.SEq.of.All_SEqGetS.Eq.Eq
open Bool Tensor


@[main]
private lemma main
  {n start stop k : ℕ}
-- given
  (h : (⟨start, stop, 1⟩ : Slice).length n = k)
  (f : ℕ → Tensor α s) :
-- imply
  ([i < n] f i)[start:stop] ≃ [i < k] f (i + start) := by
-- proof
  apply SEq.of.All_SEqGetS.Eq.Eq h rfl
  intro i
  apply SEq.of.Eq
  have hi : (i : ℕ) < stop ⊓ n - start := by
    simpa [List.LengthSlice.eq.SubMin] using i.isLt
  apply (GetGetSlice.eq.Get_Add.of.GtSubMin.fin hi ([i < n] f i)).trans
  simp [GetElem.getElem]
  apply Eq.trans (b := f (start + (i : ℕ)))
  ·
    apply EqGetStack.fun.fin (i := ⟨start + (i : ℕ), Nat.Lt.of.Lt_Min (Nat.LtAdd.of.Lt_Sub.left hi)⟩)
  ·
    rw [Nat.add_comm start]
    symm
    apply EqGetStack.fun.fin (fun t => f (t + start))


-- created on 2026-08-20
