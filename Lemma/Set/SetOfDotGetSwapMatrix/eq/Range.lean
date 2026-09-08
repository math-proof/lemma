import Lemma.Tensor.DotGetSwapMatrix.eq.Get
open Tensor


@[main]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j : Fin n) :
-- imply
  {(SwapMatrix (α := α) n ↑i ↑j)[k] @ x | (k : Fin n)} =
    Set.range (fun k : Fin n => x[k]) := by
-- proof
  have h :
      (fun k : Fin n => (SwapMatrix (α := α) n ↑i ↑j)[k] @ x) =
        (fun k : Fin n => x[k]) ∘ Equiv.swap i j := by
    funext k
    apply DotGetSwapMatrix.eq.Get
  change Set.range _ = Set.range _
  rw [h]
  exact (Equiv.swap i j).surjective.range_comp (fun k : Fin n => x[k])


-- created on 2020-07-25
-- updated on 2026-09-08
