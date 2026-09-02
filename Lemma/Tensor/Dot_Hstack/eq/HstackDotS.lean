import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.Stack.eq.AppendStackS
open Tensor
set_option maxHeartbeats 800000


/--
Matrix–matrix product distributes over column-block hstack.
-/
@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (X : Tensor α [k, p])
  (Y : Tensor α [k, q]) :
-- imply
  A @ (X.hstack Y) = (A @ X).hstack (A @ Y) := by
-- proof
  rw [Dot.eq.Stack_Sum_MulGetS A (X.hstack Y)]
  calc
    _ = ([i < n] [j < p] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) X[r][j]).hstack ([i < n] [j < q] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) Y[r][j]) := by
      apply Eq.of.All_EqGetS.fin
      intro i
      rw [EqGetStack.fin (fun i : Fin n => [j < p + q] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) (X.hstack Y)[r][j]) i]
      have hrow := GetHstack.eq.AppendGetS
        ([i < n] [j < p] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) X[r][j])
        ([i < n] [j < q] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) Y[r][j]) i
      have hXrow := EqGetStack.fin
        (fun i : Fin n => [j < p] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) X[r][j]) i
      have hYrow := EqGetStack.fin
        (fun i : Fin n => [j < q] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) Y[r][j]) i
      simp only [id] at hrow hXrow hYrow
      simp only [GetElem.getElem] at hrow
      erw [hrow]
      erw [hXrow, hYrow]
      let f : ℕ → Tensor α [] := fun j =>
        if h : j < p + q then
          ∑ r : Fin k, (id (α := Tensor α []) A[i][r]) * (id (α := Tensor α []) (id (α := Tensor α [p + q]) (X.hstack Y)[r])[j])
        else
          0
      calc
        _ = [j < p + q] f j := by
          apply Eq.of.All_EqGetS.fin
          intro j
          rw [EqGetStack.fin (fun j : Fin (p + q) => ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) (X.hstack Y)[r][j]) j]
          rw [EqGetStack.fin (fun j : Fin (p + q) => f j) j]
          simp [f, j.isLt, GetElem.getElem, id]
        _ = [j < p] f j ++ [j < q] f (p + j) :=
          Stack.eq.AppendStackS (n := p) (j := q) f
        _ = [j < p] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) X[r][j] ++ [j < q] ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) Y[r][j] := by
          apply congrArg₂ HAppend.hAppend
          ·
            apply Eq.of.All_EqGetS.fin
            intro j
            rw [EqGetStack.fin (fun j : Fin p => f j) j]
            rw [EqGetStack.fin (fun j : Fin p => ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) X[r][j]) j]
            simp only [f]
            rw [dif_pos (Nat.lt_add_right q j.isLt)]
            apply Finset.sum_congr rfl
            intro r _
            apply congrArg (HMul.hMul _)
            simpa [GetElem.getElem, id] using GetHstack.eq.Get.of.Lt j.isLt X Y r
          ·
            apply Eq.of.All_EqGetS.fin
            intro j
            rw [EqGetStack.fin (fun j : Fin q => f (p + j)) j]
            rw [EqGetStack.fin (fun j : Fin q => ∑ r : Fin k, id (α := Tensor α []) A[i][r] * id (α := Tensor α []) Y[r][j]) j]
            simp only [f]
            rw [dif_pos (Nat.add_lt_add_left j.isLt p)]
            apply Finset.sum_congr rfl
            intro r _
            apply congrArg (HMul.hMul _)
            simpa [GetElem.getElem, id] using
              GetHstack.eq.Get_Sub.of.GtAdd.Ge
                (j := p + (j : ℕ))
                (h₀ := Nat.le_add_right p j)
                (h₁ := Nat.add_lt_add_left j.isLt p) X Y r
    _ = (A @ X).hstack (A @ Y) := by
      apply congrArg₂ Tensor.hstack
      ·
        apply Eq.symm
        apply Dot.eq.Stack_Sum_MulGetS
      ·
        apply Eq.symm
        apply Dot.eq.Stack_Sum_MulGetS


-- created on 2026-09-02
