import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.Stack.eq.AppendStackS
open Tensor


/--
Vector–matrix product distributes over column-block hstack.
-/
@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (x : Tensor α [k])
  (X : Tensor α [k, p])
  (Y : Tensor α [k, q]) :
-- imply
  x @ (X.hstack Y) = id (α := Tensor α [p]) (x @ X) ++ id (α := Tensor α [q]) (x @ Y) := by
-- proof
  change id (α := Tensor α [p + q]) (x @ (X.hstack Y)) = id (α := Tensor α [p]) (x @ X) ++ id (α := Tensor α [q]) (x @ Y)
  simp only [id]
  rw [Dot.eq.Stack_Sum_MulGetS.une x (X.hstack Y), Dot.eq.Stack_Sum_MulGetS.une x X, Dot.eq.Stack_Sum_MulGetS.une x Y]
  let f : ℕ → Tensor α [] := fun j =>
    if h : j < p + q then
      ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) (id (α := Tensor α [p + q]) (X.hstack Y)[r])[j])
    else
      0
  calc
    _ = [j < p + q] f j := by
      apply Eq.of.All_EqGetS.fin
      intro j
      rw [EqGetStack.fin (fun j : Fin (p + q) => ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) (X.hstack Y)[r][j])) j]
      rw [EqGetStack.fin (fun j : Fin (p + q) => f j) j]
      simp [f, j.isLt, GetElem.getElem, id]
    _ = [j < p] f j ++ [j < q] f (p + j) :=
      Stack.eq.AppendStackS (n := p) (j := q) f
    _ = [j < p] ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) X[r][j]) ++
        [j < q] ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) Y[r][j]) := by
      apply congrArg₂ HAppend.hAppend
      ·
        apply Eq.of.All_EqGetS.fin
        intro j
        rw [EqGetStack.fin (fun j : Fin p => f j) j]
        rw [EqGetStack.fin (fun j : Fin p => ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) X[r][j])) j]
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
        rw [EqGetStack.fin (fun j : Fin q => ∑ r : Fin k, (id (α := Tensor α []) x[r]) * (id (α := Tensor α []) Y[r][j])) j]
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


-- created on 2026-09-02
