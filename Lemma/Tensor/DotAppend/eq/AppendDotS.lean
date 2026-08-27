import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqLength
import Lemma.Tensor.GetAppend.eq.Get.of.Lt
import Lemma.Tensor.GetAppend.eq.Get_Sub.of.GtAdd.Ge
import Lemma.Tensor.Stack.eq.AppendStackS
open Tensor
set_option maxHeartbeats 400000


@[main]
private lemma stack
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [m, k])
  (C : Tensor α [k, l]) :
-- imply
  [i < n + m] [j < l] ∑ p : Fin k, id (α := Tensor α []) (A ++ B)[i][p] * id (α := Tensor α []) C[p][j] = [i < n] [j < l] ∑ p : Fin k, id (α := Tensor α []) A[i][p] * id (α := Tensor α []) C[p][j] ++ [i < m] [j < l] ∑ p : Fin k, id (α := Tensor α []) B[i][p] * id (α := Tensor α []) C[p][j] := by
-- proof
  let g : ℕ → Tensor α [l] := fun i =>
    [j < l] ∑ p : Fin k,
      id (α := Tensor α [])
        (if h : i < n then
          (A.get ⟨i, by simp [Tensor.length]; exact h⟩)[p]
        else if h' : i - n < m then
          (B.get ⟨i - n, by simp [Tensor.length]; exact h'⟩)[p]
        else
          0) *
        id (α := Tensor α []) C[p][j]
  have hAB :
      [i < n + m] [j < l] ∑ p : Fin k, id (α := Tensor α []) (A ++ B)[i][p] * id (α := Tensor α []) C[p][j] =
        [i < n + m] g i := by
    apply Eq.of.All_EqGetS.fin
    intro i
    apply Eq.of.All_EqGetS.fin
    intro j
    simp [GetElem.getElem, Tensor.length]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    simp
    congr 1
    funext p
    if hi : (i : ℕ) < n then
      simp [hi]
      have hrow := GetAppend.eq.Get.of.Lt (A := A) (B := B) hi
      simp [GetElem.getElem, Tensor.length] at hrow ⊢
      rw [hrow]
      rfl
    else
      have hge : n ≤ (i : ℕ) := Nat.le_of_not_lt hi
      have hi' : (i : ℕ) - n < m := Nat.sub_lt_left_of_lt_add hge i.isLt
      simp [hi, hi']
      have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := A) (B := B) hge i.isLt
      simp [GetElem.getElem, Tensor.length] at hrow ⊢
      rw [hrow]
      rfl
  have hsplit : [i < n + m] g i = [i < n] g i ++ [i < m] g (n + i) :=
    Stack.eq.AppendStackS (n := n) (j := m) g
  have hA : [i < n] g i =
      [i < n] [j < l] ∑ p : Fin k, id (α := Tensor α []) A[i][p] * id (α := Tensor α []) C[p][j] := by
    apply Eq.of.All_EqGetS.fin
    intro i
    apply Eq.of.All_EqGetS.fin
    intro j
    simp [GetElem.getElem, Tensor.length]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    simp [GetElem.getElem, i.isLt]
    rfl
  have hB : [i < m] g (n + i) =
      [i < m] [j < l] ∑ p : Fin k, id (α := Tensor α []) B[i][p] * id (α := Tensor α []) C[p][j] := by
    apply Eq.of.All_EqGetS.fin
    intro i
    apply Eq.of.All_EqGetS.fin
    intro j
    simp [GetElem.getElem, Tensor.length]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    rw [EqGetStack.fin]
    have hlt : ¬ n + (i : ℕ) < n := Nat.not_lt_of_ge (Nat.le_add_right n i)
    have hidx : n + (i : ℕ) - n = (i : ℕ) := Nat.add_sub_cancel_left n i
    have hlenB : B.length = m := EqLength B
    simp [GetElem.getElem, hlt]
    have hget :
        B.get ⟨n + (i : ℕ) - n, by rw [hlenB, hidx]; exact i.isLt⟩ =
          B.get ⟨(i : ℕ), by rw [hlenB]; exact i.isLt⟩ := by
      congr
    rw [hget]
    convert rfl
    congr
    rfl
  rw [hAB, hsplit, hA, hB]


@[main]
private lemma main
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [m, k])
  (C : Tensor α [k, l]) :
-- imply
  (A ++ B) @ C = id (α := Tensor α [n, l]) (A @ C) ++ id (α := Tensor α [m, l]) (B @ C) := by
-- proof
  rw [Dot.eq.Stack_Sum_MulGetS (A ++ B) C]
  rw [Dot.eq.Stack_Sum_MulGetS A C]
  rw [Dot.eq.Stack_Sum_MulGetS B C]
  dsimp [HAppend.hAppend]
  have hstack := stack A B C
  simp [matmul_shape, broadcast_shape] at hstack ⊢
  exact hstack


@[main]
private lemma stack_mv
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [m, k])
  (C : Tensor α [k]) :
-- imply
  [i < n + m] ∑ p : Fin k, (id (α := Tensor α []) (A ++ B)[i][p]) * (id (α := Tensor α []) C[p]) =
    [i < n] ∑ p : Fin k, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) C[p]) ++
      [i < m] ∑ p : Fin k, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) C[p]) := by
-- proof
  let g : ℕ → Tensor α [] := fun i =>
    ∑ p : Fin k, (id (α := Tensor α [])
      (if h : i < n then
        (A.get ⟨i, by simp [Tensor.length]; exact h⟩)[p]
      else if h' : i - n < m then
        (B.get ⟨i - n, by simp [Tensor.length]; exact h'⟩)[p]
      else
        0)) *
      (id (α := Tensor α []) C[p])
  have hAB : [i < n + m] ∑ p : Fin k, (id (α := Tensor α []) (A ++ B)[i][p]) * (id (α := Tensor α []) C[p]) = [i < n + m] g i := by
    apply Eq.of.All_EqGetS.fin
    intro i
    have hL := EqGetStack.fin
      (fun i : Fin (n + m) => ∑ p : Fin k, (id (α := Tensor α []) (A ++ B)[i][p]) * (id (α := Tensor α []) C[p])) i
    have hG := EqGetStack.fin (fun i : Fin (n + m) => g i) i
    rw [hL, hG]
    simp [g]
    congr 1
    funext p
    if hi : (i : ℕ) < n then
      simp [hi]
      have hrow := GetAppend.eq.Get.of.Lt (A := A) (B := B) hi
      simp [GetElem.getElem] at hrow ⊢
      rw [hrow]
    else
      have hge : n ≤ (i : ℕ) := Nat.le_of_not_lt hi
      have hi' : (i : ℕ) - n < m := Nat.sub_lt_left_of_lt_add hge i.isLt
      simp [hi, hi']
      have hrow := GetAppend.eq.Get_Sub.of.GtAdd.Ge (A := A) (B := B) hge i.isLt
      simp [GetElem.getElem] at hrow ⊢
      rw [hrow]
  have hsplit : [i < n + m] g i = [i < n] g i ++ [i < m] g (n + i) := Stack.eq.AppendStackS (n := n) (j := m) g
  have hA : [i < n] g i = [i < n] ∑ p : Fin k, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) C[p]) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    have hL := EqGetStack.fin (fun i : Fin n => g i) i
    have hR := EqGetStack.fin
      (fun i : Fin n => ∑ p : Fin k, (id (α := Tensor α []) A[i][p]) * (id (α := Tensor α []) C[p])) i
    rw [hL, hR]
    simp [g, GetElem.getElem, i.isLt]
    rfl
  have hB : [i < m] g (n + i) = [i < m] ∑ p : Fin k, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) C[p]) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    have hL := EqGetStack.fin (fun i : Fin m => g (n + (i : ℕ))) i
    have hR := EqGetStack.fin (fun i : Fin m => ∑ p : Fin k, (id (α := Tensor α []) B[i][p]) * (id (α := Tensor α []) C[p])) i
    rw [hL, hR]
    have hlt : ¬ n + (i : ℕ) < n := Nat.not_lt_of_ge (Nat.le_add_right n i)
    have hidx : n + (i : ℕ) - n = (i : ℕ) := Nat.add_sub_cancel_left n i
    have hlenB : B.length = m := EqLength B
    simp [g, GetElem.getElem, hlt]
    have hget : B.get ⟨n + (i : ℕ) - n, by rw [hlenB, hidx]; exact i.isLt⟩ = B.get ⟨(i : ℕ), by rw [hlenB]; exact i.isLt⟩ := by
      congr
    rw [hget]
    convert rfl
    congr
  rw [hAB, hsplit, hA, hB]


/--
Matrix–vector product distributes over row-block append.
-/
@[main]
private lemma mv
  [Mul α] [AddCommMonoid α]
-- given
  (A : Tensor α [n, k])
  (B : Tensor α [m, k])
  (C : Tensor α [k]) :
-- imply
  (A ++ B) @ C = id (α := Tensor α [n]) (A @ C) ++ id (α := Tensor α [m]) (B @ C) := by
-- proof
  have hAB := Dot.eq.Stack_Sum_MulGetS.mv (A ++ B) C
  have hA := Dot.eq.Stack_Sum_MulGetS.mv A C
  have hB := Dot.eq.Stack_Sum_MulGetS.mv B C
  have hstack := stack_mv A B C
  have hcast : cast (by simp [matmul_shape]) ((A ++ B) @ C) = (cast (by simp [matmul_shape]) (A @ C) : Tensor α [n]) ++ (cast (by simp [matmul_shape]) (B @ C) : Tensor α [m]) := by
    rw [hAB, hA, hB]
    exact hstack
  have hinv : (A ++ B) @ C = cast (by simp [matmul_shape]) (cast (by simp [matmul_shape]) ((A ++ B) @ C) : Tensor α [n + m]) := by
    simp
  change (A ++ B) @ C = cast (by simp [matmul_shape]) ((cast (by simp [matmul_shape]) (A @ C) : Tensor α [n]) ++ (cast (by simp [matmul_shape]) (B @ C) : Tensor α [m]))
  rw [hinv, hcast]


-- created on 2021-11-20
-- updated on 2026-08-24
