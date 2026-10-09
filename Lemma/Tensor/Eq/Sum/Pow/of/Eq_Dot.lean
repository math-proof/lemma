import Lemma.Tensor.GetDot_SwapMatrix.eq.Get
import sympy.Basic
open Tensor


@[path]
private lemma main
  [Semiring α] [CharZero α]
  {m : ℕ}
  {x y : Tensor α [n]}
  {i j : Fin n}
-- given
  (h : x @ (SwapMatrix (α := α) n i j) = y) :
-- imply
  ∑ k : Fin n, (x[k] : Tensor α []) ^ m = ∑ k : Fin n, (y[k] : Tensor α []) ^ m := by
-- proof
  have hy : ∀ k : Fin n, (y[k] : Tensor α []) ^ m = (fun l : Fin n ↦ (x[l] : Tensor α []) ^ m) (Equiv.swap i j k) := by
    intro k
    apply Eq.trans _ (congrArg (· ^ m) (GetDot_SwapMatrix.eq.Get x i j k))
    rw [← h]
    rfl
  have hsum : (∑ k : Fin n, (y[k] : Tensor α []) ^ m) = ∑ k : Fin n, (fun l : Fin n ↦ (x[l] : Tensor α []) ^ m) (Equiv.swap i j k) :=
    Finset.sum_congr rfl (fun k _ ↦ hy k)
  rw [hsum, Equiv.sum_comp (Equiv.swap i j) (fun l : Fin n ↦ (x[l] : Tensor α []) ^ m)]


-- created on 2026-10-07
