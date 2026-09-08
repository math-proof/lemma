import Lemma.Nat.Delta.eq.Ite
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.EqMul0_0
import Lemma.Tensor.EqMul1
import Lemma.Tensor.GetSwapMatrix.eq.Ite
open Nat Tensor


/--
| attributes | lemma |
| :---: | :---: |
| main | Tensor.DotGetSwapMatrix.eq.Get |
| fin | Tensor.DotGetSwapMatrix.eq.Get.fin |
-/
@[main, fin]
private lemma main
  [Semiring α] [CharZero α]
-- given
  (x : Tensor α [n])
  (i j k : Fin n) :
-- imply
  (SwapMatrix (α := α) n ↑i ↑j)[k] @ x =
    x[Equiv.swap i j k] := by
-- proof
  apply Eq.trans (GetDot.eq.DotGet.une (SwapMatrix (α := α) n ↑i ↑j) x k).symm
  have hstack := Dot.eq.Stack_Sum_MulGetS.mv (SwapMatrix (α := α) n ↑i ↑j) x
  have hsum :
      ((SwapMatrix (α := α) n ↑i ↑j) @ x : Tensor α [n])[k] =
        ∑ m : Fin n,
          id (α := Tensor α []) (SwapMatrix (α := α) n ↑i ↑j)[k][m] *
            id (α := Tensor α []) x[m] :=
    (congrArg (fun X : Tensor α [n] => X[k]) hstack).trans
      (EqGetStack.fin
        (fun r : Fin n =>
          ∑ p : Fin n,
            id (α := Tensor α []) (SwapMatrix (α := α) n ↑i ↑j)[r][p] *
              id (α := Tensor α []) x[p])
        k)
  apply hsum.trans
  have hW (m : Fin n) :
      id (α := Tensor α []) (SwapMatrix (α := α) n ↑i ↑j)[k][m] =
        if (k : ℕ) = ↑j then
          (↑(KroneckerDelta (m : ℕ) ↑i) : Tensor α [])
        else if (k : ℕ) = ↑i then
          (↑(KroneckerDelta (m : ℕ) ↑j) : Tensor α [])
        else
          (↑(KroneckerDelta m k) : Tensor α []) := by
    simpa [id, GetElem.getElem] using GetSwapMatrix.eq.Ite (α := α) (↑i) (↑j) k m
  if hkj : (k : ℕ) = ↑j then
    have hkj' : k = j := Fin.ext hkj
    apply (Finset.sum_eq_single i ?_ ?_).trans ?_
    ·
      intro m _ hm
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[m]) (hW m)).trans
      have hm' : (m : ℕ) ≠ ↑i := Fin.val_ne_iff.mpr hm
      simp [hkj, Delta.eq.Ite, hm']
      apply Tensor.EqMul0_0.nat
    ·
      intro hi
      apply (hi (Finset.mem_univ _)).elim
    ·
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[i]) (hW i)).trans
      simp [Delta.eq.Ite, hkj', Equiv.swap_apply_right]
      apply Tensor.EqMul1.nat
  else if hki : (k : ℕ) = ↑i then
    have hki' : k = i := Fin.ext hki
    apply (Finset.sum_eq_single j ?_ ?_).trans ?_
    ·
      intro m _ hm
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[m]) (hW m)).trans
      have hm' : (m : ℕ) ≠ ↑j := Fin.val_ne_iff.mpr hm
      rw [if_neg hkj, if_pos hki]
      simp [Delta.eq.Ite, hm']
      apply Tensor.EqMul0_0.nat
    ·
      intro hj
      apply (hj (Finset.mem_univ _)).elim
    ·
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[j]) (hW j)).trans
      rw [if_neg hkj, if_pos hki, hki', Equiv.swap_apply_left]
      simp [Delta.eq.Ite]
      apply Tensor.EqMul1.nat
  else
    have hki' : k ≠ i := Fin.val_ne_iff.mp hki
    have hkj' : k ≠ j := Fin.val_ne_iff.mp hkj
    apply (Finset.sum_eq_single k ?_ ?_).trans ?_
    ·
      intro m _ hm
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[m]) (hW m)).trans
      simp [hkj, hki, Delta.eq.Ite, hm]
      apply Tensor.EqMul0_0.nat
    ·
      intro hk
      apply (hk (Finset.mem_univ _)).elim
    ·
      apply (congrArg (fun t : Tensor α [] => t * id (α := Tensor α []) x[k]) (hW k)).trans
      simp [hkj, hki, Delta.eq.Ite, Equiv.swap_apply_of_ne_of_ne hki' hkj']
      apply Tensor.EqMul1.nat


-- created on 2020-07-25
-- updated on 2026-09-08
