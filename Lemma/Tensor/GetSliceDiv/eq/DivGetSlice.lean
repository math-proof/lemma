import Lemma.Tensor.GetDiv.eq.DivGet
import Lemma.Tensor.GetGetSlice.eq.Get
open Tensor


@[main, fin]
private lemma main
  [Div α]
-- given
  (X : Tensor α (m :: s))
  (a : α)
  (n : ℕ) :
-- imply
  (X / a)[:n] = X[:n] / a := by
-- proof
  apply Eq.of.All_EqGetS.fin
  intro j
  rw [GetGetSlice.eq.Get.fin]
  have h_j := j.isLt
  simp [Tensor.length, List.LengthSlice.eq.Min] at h_j
  have hdiv_X := GetDiv.eq.DivGet.scalar.fin (X := X) (a := a) (i := ⟨j, by grind⟩)
  refine Eq.trans (congrArg (X / a).get rfl) (hdiv_X.trans ?_)
  refine (congrArg (fun t : Tensor α s => t / a) ?_).trans (DivGet.eq.GetDiv.scalar.fin X[:n] a j)
  apply Get.eq.GetGetSlice.fin


-- created on 2026-08-18
-- updated on 2026-08-19
