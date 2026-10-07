import Lemma.Finset.AscFactorial.eq.Prod
open Finset
@[main]
private lemma main
  [CommSemiring α]
  (x : α)
  {k : ℕ}
  (h : 0 < k) :
  ascFactorial x k = (x + (k - 1 : ℕ)) * ascFactorial x (k - 1) := by
  rw [AscFactorial.eq.Prod x k, AscFactorial.eq.Prod x (k - 1)]
  have hk : 0 < k := h
  cases k with
  | zero => contradiction
  | succ k' =>
    simp [Fin.prod_univ_castSucc]
    ring
-- created on 2023-08-17
