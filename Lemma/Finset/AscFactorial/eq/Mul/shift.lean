import Lemma.Finset.AscFactorial.eq.Prod
open Finset
@[path]
private lemma main
  [CommSemiring α]
  (x : α)
  {k : ℕ}
  (h : 0 < k) :
  ascFactorial x k = x * ascFactorial (x + 1) (k - 1) := by
  rw [AscFactorial.eq.Prod x k, AscFactorial.eq.Prod (x + 1) (k - 1)]
  cases k with
  | zero => contradiction
  | succ k' =>
    have h_main : (∏ i : Fin (k' + 1), (x + i)) = x * (∏ i : Fin k', (x + 1 + i)) := by
      rw [Fin.prod_univ_succAbove (fun i : Fin (k' + 1) => x + i) 0]
      have h_eq : (∏ i : Fin k', (x + (0 : Fin (k' + 1)).succAbove i)) =
          (∏ i : Fin k', (x + 1 + i)) := by
        apply Finset.prod_congr rfl
        intro i _
        have hval : (↑((0 : Fin (k' + 1)).succAbove i) : ℕ) = (↑i : ℕ) + 1 := by
          simp [Fin.succAbove]
        have hcast : ((↑((0 : Fin (k' + 1)).succAbove i) : α)) = ((↑i : α)) + 1 := by
          rw [hval, Nat.cast_add]
          simp
        simpa [hcast] using by ring
      rw [h_eq]
      simp
    exact h_main
-- created on 2023-08-17
