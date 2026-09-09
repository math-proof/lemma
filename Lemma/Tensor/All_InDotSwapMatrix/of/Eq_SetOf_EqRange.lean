import Lemma.Set.SetOfDotGetSwapMatrix.eq.Range
import Lemma.Tensor.GetDot.eq.DotGet
open Set Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
  {s : Set (Tensor α [])}
  {P : Set (Tensor α [n])}
  {i j : Fin n}
-- given
  (hP : P = {x | Set.range (fun k : Fin n => x[k]) = s}) :
-- imply
  ∀ x ∈ P, (SwapMatrix (α := α) n i j) @ x ∈ P := by
-- proof
  intro x hx
  rw [hP] at hx ⊢
  simp only [Set.mem_ofPred_eq] at hx ⊢
  have h := SetOfDotGetSwapMatrix.eq.Range (α := α) x i j
  have hget : Set.range (fun k : Fin n => ((SwapMatrix (α := α) n i j) @ x)[k]) = {(SwapMatrix (α := α) n i j)[k] @ x | (k : Fin n)} := by
    refine congrArg Set.range ?_
    funext k
    exact GetDot.eq.DotGet.une (SwapMatrix (α := α) n i j) x k
  exact hget.trans (h.trans hx)


-- created on 2020-07-26
-- updated on 2026-09-09
