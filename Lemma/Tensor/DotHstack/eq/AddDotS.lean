import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetAppend.eq.AppendGetS
import Lemma.Tensor.GetAppend.eq.Get
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.GetHstack.eq.Get.of.Lt
import Lemma.Tensor.GetHstack.eq.Get_Sub.of.GtAdd.Ge
open Tensor
set_option maxHeartbeats 400000


/--
Matrix–vector product of a column-block hstack with a split vector.
-/
@[main]
private lemma mv
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (x : Tensor α [n])
  (y : Tensor α [m]) :
-- imply
  (A.hstack B) @ (x ++ y) = id (α := Tensor α [d]) (A @ x) + id (α := Tensor α [d]) (B @ y) := by
-- proof
  change id (α := Tensor α [d]) ((A.hstack B) @ (x ++ y)) = id (α := Tensor α [d]) (A @ x) + id (α := Tensor α [d]) (B @ y)
  simp only [id]
  have hAB := Dot.eq.Stack_Sum_MulGetS.mv (A.hstack B) (x ++ y)
  have hA := Dot.eq.Stack_Sum_MulGetS.mv A x
  have hB := Dot.eq.Stack_Sum_MulGetS.mv B y
  rw [hAB, hA, hB]
  apply Eq.of.All_EqGetS.fin
  intro i
  have hrow := EqGetStack.fin (fun i : Fin d => ∑ p : Fin (n + m), (id (α := Tensor α []) (A.hstack B)[i][p]) * (id (α := Tensor α []) (x ++ y)[p])) i
  rw [hrow]
  have hadd := GetAdd.eq.AddGetS.fin
    ([i < d] ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) x[p]))
    ([i < d] ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) y[p])) i
  rw [hadd]
  have hsumA := EqGetStack.fin (fun i : Fin d => ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) x[p])) i
  have hsumB := EqGetStack.fin (fun i : Fin d => ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) y[p])) i
  rw [hsumA, hsumB]
  let Ai : Tensor α [n] := A[i]
  let Bi : Tensor α [m] := B[i]
  let A' : Tensor α ([d] ++ n :: []) := A
  let B' : Tensor α ([d] ++ m :: []) := B
  have happ := GetAppend.eq.AppendGetS A' B' i
  simp only [id] at happ
  have hsplit : (A.hstack B)[i] = Ai ++ Bi := by
    have h : A.hstack B = A' ++ B' := rfl
    have h1 : (A.hstack B)[i] = (A' ++ B')[i] := congrArg (fun X : Tensor α [d, n + m] => X[i]) h
    exact h1.trans (happ.trans (by simp [Ai, Bi, A', B', GetElem.getElem]))
  change ∑ p : Fin (n + m), (id (α := Tensor α []) (A.hstack B)[i][p]) * (id (α := Tensor α []) (x ++ y)[p]) = Add.add (∑ p : Fin n, (id (α := Tensor α []) Ai[p]) * (id (α := Tensor α []) x[p])) (∑ p : Fin m, (id (α := Tensor α []) Bi[p]) * (id (α := Tensor α []) y[p]))
  rw [hsplit]
  let f : Fin (n + m) → Tensor α [] := fun p => (id (α := Tensor α []) (Ai ++ Bi)[p]) * (id (α := Tensor α []) (x ++ y)[p])
  have hsum := Fintype.sum_equiv finSumFinEquiv (fun s : Fin n ⊕ Fin m => f (finSumFinEquiv s)) f (fun _ => rfl)
  have hsum_split : ∑ p : Fin (n + m), f p = Add.add (∑ p : Fin n, f (finSumFinEquiv (Sum.inl p))) (∑ p : Fin m, f (finSumFinEquiv (Sum.inr p))) := by
    rw [← hsum, Fintype.sum_sum_type]
    rfl
  refine Eq.trans hsum_split ?_
  refine congrArg₂ Add.add ?_ ?_
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_left]
    have hX' : (Ai ++ Bi)[Fin.castAdd m p] = Ai[p] := by
      have h := GetAppend.eq.Get.fin Ai Bi p
      simp [GetElem.getElem, Fin.castAdd] at h ⊢
      rw [h]
      exact congrArg Ai.get (Eq.symm (Fin.eta p p.isLt))
    have hx' : (x ++ y)[Fin.castAdd m p] = x[p] := by
      have h := GetAppend.eq.Get.fin x y p
      simp [GetElem.getElem, Fin.castAdd] at h ⊢
      rw [h]
      exact congrArg x.get (Eq.symm (Fin.eta p p.isLt))
    rw [hX', hx']
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_right]
    have hY' : (Ai ++ Bi)[Fin.natAdd n p] = Bi[p] := by
      have h := GetAppend.eq.Get_Sub.of.GtAdd.Ge
        (i := n + (p : ℕ))
        (h₀ := Nat.le_add_right n p)
        (h₁ := Nat.add_lt_add_left p.isLt n) Ai Bi
      simp [GetElem.getElem, Fin.natAdd] at h ⊢
      exact h
    have hy' : (x ++ y)[Fin.natAdd n p] = y[p] := by
      have h := GetAppend.eq.Get_Sub.of.GtAdd.Ge
        (i := n + (p : ℕ))
        (h₀ := Nat.le_add_right n p)
        (h₁ := Nat.add_lt_add_left p.isLt n) x y
      simp [GetElem.getElem, Fin.natAdd] at h ⊢
      exact h
    rw [hY', hy']


/--
Matrix–matrix product of a column-block hstack with a row-block append.
-/
@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [d, n])
  (B : Tensor α [d, m])
  (X : Tensor α [n, r])
  (Y : Tensor α [m, r]) :
-- imply
  (A.hstack B) @ (X ++ Y) = id (α := Tensor α [d, r]) (A @ X) + id (α := Tensor α [d, r]) (B @ Y) := by
-- proof
  change id (α := Tensor α [d, r]) ((A.hstack B) @ (X ++ Y)) = id (α := Tensor α [d, r]) (A @ X) + id (α := Tensor α [d, r]) (B @ Y)
  simp only [id]
  have hAB := Dot.eq.Stack_Sum_MulGetS (A.hstack B) (X ++ Y)
  have hA := Dot.eq.Stack_Sum_MulGetS A X
  have hB := Dot.eq.Stack_Sum_MulGetS B Y
  rw [hAB, hA, hB]
  apply Eq.of.All_EqGetS.fin
  intro i
  have hrow := EqGetStack.fin (fun i : Fin d => [j < r] ∑ p : Fin (n + m), (id (α := Tensor α []) (A.hstack B)[i][p]) * (id (α := Tensor α []) (X ++ Y)[p][j])) i
  rw [hrow]
  have hadd := GetAdd.eq.AddGetS.fin
    ([i < d] [j < r] ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) X[p][j]))
    ([i < d] [j < r] ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) Y[p][j])) i
  rw [hadd]
  have hsumA := EqGetStack.fin (fun i : Fin d => [j < r] ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) X[p][j])) i
  have hsumB := EqGetStack.fin (fun i : Fin d => [j < r] ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) Y[p][j])) i
  rw [hsumA, hsumB]
  apply Eq.of.All_EqGetS.fin
  intro j
  have hLj := EqGetStack.fin (fun j : Fin r => ∑ p : Fin (n + m), (id (α := Tensor α []) (A.hstack B)[i][p]) * (id (α := Tensor α []) (X ++ Y)[p][j])) j
  have hAj := EqGetStack.fin
    (fun j : Fin r => ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) X[p][j])) j
  have hBj := EqGetStack.fin
    (fun j : Fin r => ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) Y[p][j])) j
  have haddj := GetAdd.eq.AddGetS.fin
    ([j < r] ∑ p : Fin n, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) X[p][j]))
    ([j < r] ∑ p : Fin m, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) Y[p][j])) j
  rw [hLj]
  erw [haddj, hAj, hBj]
  let f : Fin (n + m) → Tensor α [] := fun p =>
    (id (α := Tensor α []) (A.hstack B)[i][p]) * (id (α := Tensor α []) (X ++ Y)[p][j])
  have hsum := Fintype.sum_equiv finSumFinEquiv (fun s : Fin n ⊕ Fin m => f (finSumFinEquiv s)) f (fun _ => rfl)
  have hsum_split : ∑ p : Fin (n + m), f p = Add.add (∑ p : Fin n, f (finSumFinEquiv (Sum.inl p))) (∑ p : Fin m, f (finSumFinEquiv (Sum.inr p))) := by
    rw [← hsum, Fintype.sum_sum_type]
    rfl
  refine Eq.trans hsum_split ?_
  refine congrArg₂ Add.add ?_ ?_
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_left]
    have hA' := GetHstack.eq.Get.of.Lt p.isLt A B i
    simp only [id] at hA'
    apply congrArg₂ HMul.hMul
    ·
      simpa [GetElem.getElem, Fin.castAdd] using hA'
    ·
      have hX' := GetAppend.eq.Get.fin X Y p
      have hX'' : (X ++ Y).get ⟨(p : ℕ), Nat.lt_add_right m p.isLt⟩ = X.get ⟨(p : ℕ), p.isLt⟩ :=
        hX'.trans (congrArg X.get (Eq.symm (Fin.eta p p.isLt)))
      simpa [GetElem.getElem, Fin.castAdd] using congrArg (fun t : Tensor α [r] => t.get ⟨(j : ℕ), j.isLt⟩) hX''
  ·
    apply Finset.sum_congr rfl
    intro p _
    simp only [f, id, finSumFinEquiv_apply_right]
    have hB' := GetHstack.eq.Get_Sub.of.GtAdd.Ge
      (j := n + (p : ℕ))
      (h₀ := Nat.le_add_right n p)
      (h₁ := Nat.add_lt_add_left p.isLt n) A B i
    simp only [id] at hB'
    apply congrArg₂ HMul.hMul
    ·
      simpa [GetElem.getElem, Fin.natAdd] using hB'
    ·
      have hY' := GetAppend.eq.Get_Sub.of.GtAdd.Ge
        (i := n + (p : ℕ))
        (h₀ := Nat.le_add_right n p)
        (h₁ := Nat.add_lt_add_left p.isLt n) X Y
      simp at hY'
      simpa [GetElem.getElem, Fin.natAdd] using congrArg (fun t : Tensor α [r] => t.get ⟨(j : ℕ), j.isLt⟩) hY'


-- created on 2026-08-23
-- updated on 2026-09-02
