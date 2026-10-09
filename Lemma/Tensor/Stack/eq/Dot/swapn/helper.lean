import sympy.concrete.products
import sympy.matrices.expressions.permutation
import sympy.vector.Basic
import Lemma.Tensor.GetDot_SwapMatrix.eq.Get
import Lemma.Tensor.DotDot.eq.Dot_Dot
import Lemma.Tensor.EqDot_Eye
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
open Tensor
set_option maxHeartbeats 4000000


@[path]
private lemma main
  [Semiring α] [CharZero α]
  {n m : ℕ}
-- given
  (hmn : m ≤ n)
  (d : Fin m → Fin n)
  (x : Tensor α [n]) :
-- imply
  [k < n]
    x[Fin.foldl m (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) => σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 k] =
    x @ matProd m (fun i => SwapMatrix (α := α) n (i : ℕ) (d i)) := by
-- proof
  have key : ∀ m : ℕ, ∀ (hmn : m ≤ n) (d : Fin m → Fin n) (k : Fin n),
      x[Fin.foldl m (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) => σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 k] =
        (x @ matProd m (fun i => SwapMatrix (α := α) n (i : ℕ) (d i)))[k] := by
    intro m
    induction m with
    | zero =>
      intro hmn d k
      exact (congrArg (fun t : Tensor α [n] => t[k]) (EqDot_Eye.vm x)).symm
    | succ m ih =>
      intro hmn d k
      have hmp : matProd (m + 1) (fun i => SwapMatrix (α := α) n (i : ℕ) (d i)) =
        (matProd m (fun i => SwapMatrix (α := α) n (i : ℕ) (d i.castSucc))) @ (SwapMatrix (α := α) n (Fin.castLE hmn (Fin.last m)) (d (Fin.last m))) := rfl
      have hfold : Fin.foldl (m + 1) (fun (σ : Equiv.Perm (Fin n)) (i : Fin (m + 1)) => σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 =
        (Fin.foldl m (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) => σ * Equiv.swap (Fin.castLE hmn i.castSucc) (d i.castSucc)) 1) * Equiv.swap (Fin.castLE hmn (Fin.last m)) (d (Fin.last m)) := by
        rw [Fin.foldl_succ_last]
      apply Eq.trans
      · exact congrArg (fun idx : Fin n => x[idx])
          (Eq.trans (congrArg (fun σ : Equiv.Perm (Fin n) => σ k) hfold) (Equiv.Perm.mul_apply _ _ k))
      ·
        apply Eq.trans
        · exact ih (Nat.le_of_succ_le hmn) (fun i => d i.castSucc) _
        ·
          apply Eq.trans
          · exact (GetDot_SwapMatrix.eq.Get (x @ matProd m (fun i => SwapMatrix (α := α) n (i : ℕ) (d i.castSucc))) (Fin.castLE hmn (Fin.last m)) (d (Fin.last m)) k).symm
          ·
            apply Eq.trans
            · exact congrArg (fun t : Tensor α [n] => t[k]) (DotDot.eq.Dot_Dot.vmm x (matProd m (fun i => SwapMatrix (α := α) n (i : ℕ) (d i.castSucc))) (SwapMatrix (α := α) n (Fin.castLE hmn (Fin.last m)) (d (Fin.last m))))
            · exact congrArg (fun t : Tensor α [n] => t[k]) (congrArg (fun t : Tensor α [n, n] => x @ t) hmp.symm)
  apply Eq.of.All_EqGetS
  intro k
  rw [EqGetStack (fun k => x[Fin.foldl m (fun (σ : Equiv.Perm (Fin n)) (i : Fin m) => σ * Equiv.swap (Fin.castLE hmn i) (d i)) 1 k]) k]
  apply key m hmn d k


-- created on 2026-10-08
