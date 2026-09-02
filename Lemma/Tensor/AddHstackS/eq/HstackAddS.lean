import Lemma.Tensor.AddAppendS.eq.AppendAddS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetAdd.eq.AddGetS
import Lemma.Tensor.GetHstack.eq.AppendGetS
open Tensor
set_option maxHeartbeats 400000


@[main, comm]
private lemma main
  [Add α]
-- given
  (A C : Tensor α [d, n])
  (B D : Tensor α [d, m]) :
-- imply
  (A.hstack B) + (C.hstack D) = (A + C).hstack (B + D) := by
-- proof
  have hAB : A.hstack B = [i < d] (id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    exact (GetHstack.eq.AppendGetS A B i).trans
      (EqGetStack.fin (fun i : Fin d => id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) i).symm
  have hCD : C.hstack D = [i < d] (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i]) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    exact (GetHstack.eq.AppendGetS C D i).trans
      (EqGetStack.fin (fun i : Fin d => id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i]) i).symm
  have hAD : (A + C).hstack (B + D) = [i < d] (id (α := Tensor α [n]) (A + C)[i] ++ id (α := Tensor α [m]) (B + D)[i]) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    exact (GetHstack.eq.AppendGetS (A + C) (B + D) i).trans
      (EqGetStack.fin (fun i : Fin d => id (α := Tensor α [n]) (A + C)[i] ++ id (α := Tensor α [m]) (B + D)[i]) i).symm
  rw [hAB, hCD, hAD]
  have hadd :
      ([i < d] (id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i])) +
        ([i < d] (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i])) =
      [i < d]
        ((id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) +
          (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i])) := by
    apply Eq.of.All_EqGetS.fin
    intro i
    have hL := GetAdd.eq.AddGetS.fin
      ([i < d] (id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]))
      ([i < d] (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i])) i
    have hf := EqGetStack.fin (fun i : Fin d => id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) i
    have hg := EqGetStack.fin (fun i : Fin d => id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i]) i
    have hfg := EqGetStack.fin
      (fun i : Fin d =>
        (id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) +
          (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i])) i
    exact hL.trans ((congrArg₂ HAdd.hAdd hf hg).trans hfg.symm)
  rw [hadd]
  apply Eq.of.All_EqGetS.fin
  intro i
  have hL := EqGetStack.fin
    (fun i : Fin d =>
      (id (α := Tensor α [n]) A[i] ++ id (α := Tensor α [m]) B[i]) +
        (id (α := Tensor α [n]) C[i] ++ id (α := Tensor α [m]) D[i])) i
  have hR := EqGetStack.fin
    (fun i : Fin d => id (α := Tensor α [n]) (A + C)[i] ++ id (α := Tensor α [m]) (B + D)[i]) i
  rw [hL, hR]
  have hsum :=
    AddAppendS.eq.AppendAddS
      (A := id (α := Tensor α [n]) A[i])
      (C := id (α := Tensor α [n]) C[i])
      (B := id (α := Tensor α [m]) B[i])
      (D := id (α := Tensor α [m]) D[i])
  have hAC : id (α := Tensor α [n]) (A + C)[i] =
      id (α := Tensor α [n]) A[i] + id (α := Tensor α [n]) C[i] := by
    simp only [id]
    have h := GetAdd.eq.AddGetS.fin A C ⟨i, by simp⟩
    simp [GetElem.getElem] at h ⊢
    exact h
  have hBD : id (α := Tensor α [m]) (B + D)[i] =
      id (α := Tensor α [m]) B[i] + id (α := Tensor α [m]) D[i] := by
    simp only [id]
    have h := GetAdd.eq.AddGetS.fin B D ⟨i, by simp⟩
    simp [GetElem.getElem] at h ⊢
    exact h
  simp only [id] at hsum hAC hBD ⊢
  rw [hsum, hAC, hBD]


-- created on 2026-09-01
