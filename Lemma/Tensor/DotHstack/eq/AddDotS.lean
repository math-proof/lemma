import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetAppend.eq.AppendGetS
import Lemma.Tensor.GetAppend.eq.Get
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
open Tensor
set_option maxHeartbeats 400000


private lemma sum_append_mul
  [Mul α] [AddCommMonoid α]
-- given
  (X : Tensor α [n])
  (Y : Tensor α [m])
  (x : Tensor α [n])
  (y : Tensor α [m]) :
-- imply
  ∑ p : Fin (n + m),
      (id (α := Tensor α []) (X ++ Y)[p]) * (id (α := Tensor α []) (x ++ y)[p]) =
    Add.add
      (∑ p : Fin n, (id (α := Tensor α []) X[p]) * (id (α := Tensor α []) x[p]))
      (∑ p : Fin m, (id (α := Tensor α []) Y[p]) * (id (α := Tensor α []) y[p])) := by
-- proof
  let f : Fin (n + m) → Tensor α [] := fun p =>
    (id (α := Tensor α []) (X ++ Y)[p]) * (id (α := Tensor α []) (x ++ y)[p])
  have hsum :=
    Fintype.sum_equiv finSumFinEquiv
      (fun s : Fin n ⊕ Fin m => f (finSumFinEquiv s)) f (fun _ => rfl)
  have hsplit :
      ∑ p : Fin (n + m), f p =
        Add.add
          (∑ p : Fin n, f (finSumFinEquiv (Sum.inl p)))
          (∑ p : Fin m, f (finSumFinEquiv (Sum.inr p))) := by
    rw [← hsum, Fintype.sum_sum_type]
    rfl
  refine Eq.trans hsplit ?_
  refine congrArg₂ Add.add ?_ ?_
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_left]
    have hX' : (X ++ Y)[Fin.castAdd m p] = X[p] := by
      simp [GetElem.getElem]
      simpa [Fin.castAdd] using GetAppend.eq.Get.fin X Y p
    have hx' : (x ++ y)[Fin.castAdd m p] = x[p] := by
      simp [GetElem.getElem]
      simpa [Fin.castAdd] using GetAppend.eq.Get.fin x y p
    rw [hX', hx']
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_right]
    have hY' : (X ++ Y)[Fin.natAdd n p] = Y[p] := by
      have h :=
        GetAppend.eq.Get_Sub.of.GtAdd.Ge
          (i := n + (p : ℕ))
          (h₀ := Nat.le_add_right n p)
          (h₁ := Nat.add_lt_add_left p.isLt n) X Y
      simp [GetElem.getElem, Fin.natAdd] at h ⊢
      exact h
    have hy' : (x ++ y)[Fin.natAdd n p] = y[p] := by
      have h :=
        GetAppend.eq.Get_Sub.of.GtAdd.Ge
          (i := n + (p : ℕ))
          (h₀ := Nat.le_add_right n p)
          (h₁ := Nat.add_lt_add_left p.isLt n) x y
      simp [GetElem.getElem, Fin.natAdd] at h ⊢
      exact h
    rw [hY', hy']


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (x : Tensor α [n])
  (y : Tensor α [m]) :
-- imply
  (Tensor.hstack A B) @ (x ++ y) = id (α := Tensor α [d]) (A @ x) + id (α := Tensor α [d]) (B @ y) := by
-- proof
  change
    id (α := Tensor α [d]) ((Tensor.hstack A B) @ (x ++ y)) =
      id (α := Tensor α [d]) (A @ x) + id (α := Tensor α [d]) (B @ y)
  simp only [id]
  have hAB := Dot.eq.Stack_Sum_MulGetS.mv (Tensor.hstack A B) (x ++ y)
  have hA := Dot.eq.Stack_Sum_MulGetS.mv A x
  have hB := Dot.eq.Stack_Sum_MulGetS.mv B y
  rw [hAB, hA, hB]
  apply Eq.of.All_EqGetS.fin
  intro i
  have hrow := EqGetStack.fin
    (fun i : Fin d => ∑ p : Fin (n + m),
      (id (α := Tensor α []) (Tensor.hstack A B)[i][p]) * (id (α := Tensor α []) (x ++ y)[p])) i
  rw [hrow]
  have hadd := GetAdd.eq.AddGetS.fin
    ([i < d] ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) x[p]))
    ([i < d] ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) y[p])) i
  rw [hadd]
  have hsumA := EqGetStack.fin
    (fun i : Fin d => ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) x[p])) i
  have hsumB := EqGetStack.fin
    (fun i : Fin d => ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) y[p])) i
  rw [hsumA, hsumB]
  let Ai : Tensor α [n] := A[i]
  let Bi : Tensor α [m] := B[i]
  let A' : Tensor α ([d] ++ n :: []) := A
  let B' : Tensor α ([d] ++ m :: []) := B
  have happ := GetAppend.eq.AppendGetS A' B' i
  simp only [id] at happ
  have hsplit : (Tensor.hstack A B)[i] = Ai ++ Bi := by
    have h : Tensor.hstack A B = A' ++ B' := rfl
    have h1 : (Tensor.hstack A B)[i] = (A' ++ B')[i] :=
      congrArg (fun X : Tensor α [d, n + m] => X[i]) h
    exact h1.trans (happ.trans (by simp [Ai, Bi, A', B', GetElem.getElem]))
  change
    ∑ p : Fin (n + m),
        (id (α := Tensor α []) (Tensor.hstack A B)[i][p]) * (id (α := Tensor α []) (x ++ y)[p]) =
      Add.add
        (∑ p : Fin n, (id (α := Tensor α []) Ai[p]) * (id (α := Tensor α []) x[p]))
        (∑ p : Fin m, (id (α := Tensor α []) Bi[p]) * (id (α := Tensor α []) y[p]))
  rw [hsplit]
  exact sum_append_mul Ai Bi x y


-- created on 2026-08-23
-- updated on 2026-08-24
