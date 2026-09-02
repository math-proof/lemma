import Lemma.Nat.Delta.eq.Ite
import Lemma.Nat.EqCast_0'0
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGet0_0
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqStack_0'0
import Lemma.Tensor.GetAppend.eq.AppendGetS
import Lemma.Tensor.Stack.eq.AppendStackS
import Lemma.Tensor.Stack.eq.Eye
open Nat Tensor
set_option maxHeartbeats 400000


private lemma delta_fin_nat
  (i j : Fin n) :
  KroneckerDelta i j = KroneckerDelta (i : ℕ) (j : ℕ) := by
  simp [KroneckerDelta, Fin.ext_iff]


@[main]
private lemma main
  [AddMonoidWithOne α] [CharZero α]
-- given
  (n m : ℕ) :
-- imply
  (Tensor.eye n).hstack (0 : Tensor α [n, m]) ++ (0 : Tensor α [m, n]).hstack (Tensor.eye m) = Tensor.eye (n + m) := by
-- proof
  let In : Tensor α [n, n] := Tensor.eye n
  let Znm : Tensor α [n, m] := 0
  let Zmn : Tensor α [m, n] := 0
  let Im : Tensor α [m, m] := Tensor.eye m
  let In' : Tensor α ([n] ++ n :: []) := In
  let Znm' : Tensor α ([n] ++ m :: []) := Znm
  let Zmn' : Tensor α ([m] ++ n :: []) := Zmn
  let Im' : Tensor α ([m] ++ m :: []) := Im
  let row0 : Tensor α [n, n + m] := In.hstack Znm
  let row1 : Tensor α [m, n + m] := Zmn.hstack Im
  have hrow0 : row0 = In' ++ Znm' := rfl
  have hrow1 : row1 = Zmn' ++ Im' := rfl
  change row0 ++ row1 = Tensor.eye (n + m)
  rw [← Stack.eq.Eye (α := α) (n := n + m)]
  have hδ :
      [i < n + m] [j < n + m] (↑(KroneckerDelta i j) : Tensor α []) =
        [i < n + m] [j < n + m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    apply Eq.of.All_EqGetS.fin
    intro j
    have hi := EqGetStack.fin (fun i : Fin (n + m) => [j < n + m] (↑(KroneckerDelta i j) : Tensor α [])) i
    have hj := EqGetStack.fin (fun j : Fin (n + m) => (↑(KroneckerDelta i j) : Tensor α [])) j
    have hi' := EqGetStack.fin (fun i : Fin (n + m) => [j < n + m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) i
    have hj' := EqGetStack.fin (fun j : Fin (n + m) => (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) j
    simp at hi hj hi' hj' ⊢
    rw [hi, hj, hi', hj']
    simp [delta_fin_nat]
  rw [hδ]
  have hsplit :=
    Stack.eq.AppendStackS (n := n) (j := m)
      (fun i => [j < n + m] (↑(KroneckerDelta i (j : ℕ)) : Tensor α []))
  rw [hsplit]
  have h0 : row0 = [i < n] [j < n + m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    rw [hrow0]
    show
      id (α := Tensor α [n + m]) (In' ++ Znm')[i] =
        id (α := Tensor α [n + m])
          ([i < n] [j < n + m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []))[i]
    have happ := GetAppend.eq.AppendGetS (A := In') (B := Znm') i
    simp only [id] at happ ⊢
    rw [happ]
    have hIn : In'[i] = [j < n] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []) := by
      simp [In', In, Tensor.eye]
      have h := EqGetStack.fin (fun i : Fin n => [j < n] (↑(KroneckerDelta i j) : Tensor α [])) i
      simp [GetElem.getElem] at h ⊢
      erw [h]
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL := EqGetStack.fin (fun j : Fin n => (↑(KroneckerDelta i j) : Tensor α [])) j
      have hR := EqGetStack.fin (fun j : Fin n => (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) j
      simp at hL hR ⊢
      rw [hL, hR]
      simp [delta_fin_nat]
    have hZ : Znm'[i] = (0 : Tensor α [m]) := by
      simp [Znm', Znm]
      convert EqGet0_0.fin (α := α) (s := ([n] ++ m :: [])) ⟨(i : ℕ), by simp [Tensor.length]⟩
      · rfl
      · simp [GetElem.getElem]
        congr
      · rfl
    rw [hIn, hZ]
    have h0stack : (0 : Tensor α [m]) = [j < m] (0 : Tensor α []) :=
      (EqStack_0'0 (α := α) [] m).symm
    rw [h0stack]
    have hzero : [j < m] (0 : Tensor α []) = [j < m] (↑(KroneckerDelta (i : ℕ) (n + (j : ℕ))) : Tensor α []) := by
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL := EqGetStack.fin (fun _ : Fin m => (0 : Tensor α [])) j
      have hR := EqGetStack.fin (fun j : Fin m => (↑(KroneckerDelta (i : ℕ) (n + (j : ℕ))) : Tensor α [])) j
      simp at hL hR ⊢
      rw [hL, hR]
      simp [Delta.eq.Ite]
      split_ifs with h
      ·
        have : (i : ℕ) < n := i.isLt
        omega
      ·
        exact (EqCast_0'0 (R := Tensor α [])).symm
    rw [hzero]
    have hget := EqGetStack.fin (fun i : Fin n => [j < n + m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) i
    simp [GetElem.getElem] at hget ⊢
    erw [hget]
    symm
    apply Stack.eq.AppendStackS (fun j => (↑(KroneckerDelta (i : ℕ) j) : Tensor α []))
  have h1 : row1 = [i < m] [j < n + m] (↑(KroneckerDelta (n + (i : ℕ)) (j : ℕ)) : Tensor α []) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    rw [hrow1]
    show id (α := Tensor α [n + m]) (Zmn' ++ Im')[i] = id (α := Tensor α [n + m]) ([i < m] [j < n + m] (↑(KroneckerDelta (n + (i : ℕ)) (j : ℕ)) : Tensor α []))[i]
    have happ := GetAppend.eq.AppendGetS (A := Zmn') (B := Im') i
    simp only [id] at happ ⊢
    rw [happ]
    have hZ : Zmn'[i] = (0 : Tensor α [n]) := by
      simp [Zmn', Zmn]
      convert EqGet0_0.fin (α := α) (s := ([m] ++ n :: [])) ⟨(i : ℕ), by simp [Tensor.length]⟩
      · rfl
      · simp [GetElem.getElem]
        congr
      · rfl
    have hIm : Im'[i] = [j < m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []) := by
      simp [Im', Im, Tensor.eye]
      have h := EqGetStack.fin (fun i : Fin m => [j < m] (↑(KroneckerDelta i j) : Tensor α [])) i
      simp [GetElem.getElem] at h ⊢
      erw [h]
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL := EqGetStack.fin (fun j : Fin m => (↑(KroneckerDelta i j) : Tensor α [])) j
      have hR := EqGetStack.fin (fun j : Fin m => (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) j
      simp at hL hR ⊢
      rw [hL, hR]
      simp [delta_fin_nat]
    rw [hZ, hIm]
    have h0stack : (0 : Tensor α [n]) = [j < n] (0 : Tensor α []) :=
      (EqStack_0'0 (α := α) [] n).symm
    rw [h0stack]
    have hzero :
        [j < n] (0 : Tensor α []) =
          [j < n] (↑(KroneckerDelta (n + (i : ℕ)) (j : ℕ)) : Tensor α []) := by
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL := EqGetStack.fin (fun _ : Fin n => (0 : Tensor α [])) j
      have hR := EqGetStack.fin (fun j : Fin n => (↑(KroneckerDelta (n + (i : ℕ)) (j : ℕ)) : Tensor α [])) j
      simp at hL hR ⊢
      rw [hL, hR]
      simp [Delta.eq.Ite]
      split_ifs with h
      ·
        omega
      ·
        exact (EqCast_0'0 (R := Tensor α [])).symm
    have heye : [j < m] (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α []) = [j < m] (↑(KroneckerDelta (n + (i : ℕ)) (n + (j : ℕ))) : Tensor α []) := by
      apply Eq.of.All_EqGetS.fin
      intro j
      have hL := EqGetStack.fin (fun j : Fin m => (↑(KroneckerDelta (i : ℕ) (j : ℕ)) : Tensor α [])) j
      have hR := EqGetStack.fin (fun j : Fin m => (↑(KroneckerDelta (n + (i : ℕ)) (n + (j : ℕ))) : Tensor α [])) j
      simp at hL hR ⊢
      rw [hL, hR]
      simp [KroneckerDelta, Nat.add_left_cancel_iff]
    rw [hzero, heye]
    have hget := EqGetStack.fin
      (fun i : Fin m => [j < n + m] (↑(KroneckerDelta (n + (i : ℕ)) (j : ℕ)) : Tensor α [])) i
    simp [GetElem.getElem] at hget ⊢
    erw [hget]
    symm
    apply Stack.eq.AppendStackS (fun j => (↑(KroneckerDelta (n + (i : ℕ)) j) : Tensor α []))
  rw [h0, h1]


-- created on 2023-06-16
-- updated on 2026-08-24
