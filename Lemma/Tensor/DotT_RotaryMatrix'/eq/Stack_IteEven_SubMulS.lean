import Lemma.List.EqSwap_0'1
import Lemma.Tensor.Add
import Lemma.Tensor.AddMulS.eq.SubMulS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.EqGetT
import Lemma.Tensor.GetCast.as.Get.of.Eq.GtLength_0
import Lemma.Tensor.SEqGetS.of.SEq.GtLength
import Lemma.Bool.SEq.is.Eq
import Lemma.Bool.EqCast.of.SEq
import Lemma.Bool.SEqCast.of.Eq
import Lemma.Tensor.GetRotaryMatrix'.eq.Ite_IteS
import Lemma.Tensor.Mul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.Sub.eq.Add_Neg
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSub.eq.SubGet
import torch.Tensor.permute
import torch.Tensor
import torch.functions
import torch.stack
open Bool Tensor List
set_option maxHeartbeats 8000000


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (x : Tensor ℝ [d + d]) :
-- imply
  θ.rotaryMatrix'ᵀ @ x =
    [j < d + d]
      if h : (j : ℕ) % 2 = 0 then
        let j1 : Fin (d + d) := ⟨(j : ℕ) + 1, by omega⟩
        id (α := Tensor ℝ []) (x[j]) *
            id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(by grind)) +
          id (α := Tensor ℝ []) (x[j1]) *
            id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(by grind))
      else
        let j0 : Fin (d + d) := ⟨(j : ℕ) - 1, by omega⟩
        id (α := Tensor ℝ []) (x[j]) *
            id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(by grind)) -
          id (α := Tensor ℝ []) (x[j0]) *
            id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(by grind)) := by
-- proof
  let RT : Tensor ℝ [d + d, d + d] :=
    cast (congrArg (Tensor ℝ) (by simp)) θ.rotaryMatrix'ᵀ
  have hmat : θ.rotaryMatrix'ᵀ @ x = RT @ x := by
    refine congrArg (fun t : Tensor ℝ [d + d, d + d] => t @ x) ?_
    exact (cast_eq (congrArg (Tensor ℝ) (by simp)) θ.rotaryMatrix'ᵀ).symm
  rw [hmat]
  apply Eq.trans (Dot.eq.Stack_Sum_MulGetS.mv RT x)
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [EqGetStack.fin (i := j)]
  conv_rhs => erw [EqGetStack.fin (i := j)]
  have hTget (k : Fin (d + d)) : RT[j][k] = θ.rotaryMatrix'[k][j] := by
    have hEqT : θ.rotaryMatrix'ᵀ[j][k] = θ.rotaryMatrix'[k][j] :=
      EqGetT.fin θ.rotaryMatrix' k j
    refine Eq.trans ?_ hEqT
    simp only [RT]
    have hrow :=
      GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
        (by simp : ([d + d, d + d] : List ℕ).length > 0)
        (by simp)
        θ.rotaryMatrix'ᵀ
        j
    have hcell := congrArg (fun t : Tensor ℝ _ => t[k]) hrow
    refine Eq.trans hcell ?_
    have hrow_shape :
        (([d + d, d + d].swap ([d + d, d + d].length - 2) ([d + d, d + d].length - 1)).tail) =
          [d + d] := by
      simp
    have hcell' :=
      GetCast.eq.Cast_Get.of.Eq.GtLength_0.right.fin
        (by simp : ([d + d] : List ℕ).length > 0)
        hrow_shape
        (θ.rotaryMatrix'ᵀ[j])
        k
    exact hcell'.trans (cast_eq _ _)
  simp_rw [hTget]
  split_ifs with hj
  · let j1 : Fin (d + d) := ⟨(j : ℕ) + 1, by omega⟩
    have hj1ne : j ≠ j1 := Fin.ne_of_val_ne (by simp [j1])
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[k][j]) *
            id (α := Tensor ℝ []) (x[k]))
        j j1 (Finset.mem_univ _) (Finset.mem_univ _) hj1ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hne0 : (k : ℕ) ≠ (j : ℕ) := Fin.val_ne_iff.mpr hk0
      have hne1 : (k : ℕ) ≠ (j : ℕ) + 1 := by
        intro h; exact hk1 (Fin.ext (by simpa [j1] using h))
      have hk' :
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[k][j]) =
            id (α := Tensor ℝ []) (0 : Tensor ℝ []) := by
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ k j
        by_cases hk_even : (k : ℕ) % 2 = 0
        · simp only [hk_even, ↓reduceIte] at hk
          have hjk : (j : ℕ) ≠ (k : ℕ) := Ne.symm hne0
          have hjk1 : (j : ℕ) ≠ (k : ℕ) + 1 := by
            intro h
            have : (k : ℕ) % 2 = 1 := by omega
            exact Nat.mod_two_ne_one.mpr hk_even this
          simpa [hjk, hjk1, id] using hk
        · simp only [hk_even, ↓reduceIte] at hk
          have hjk : (j : ℕ) ≠ (k : ℕ) := Ne.symm hne0
          have hjk1 : (j : ℕ) + 1 ≠ (k : ℕ) := by
            intro h; exact hne1 h.symm
          simpa [hjk, hjk1, id] using hk
      rw [hk']
      simp only [id_eq]
      rw [Tensor.Mul]
      exact zero_mul _
    · set c : Tensor ℝ [] := (θ.cos[(j : ℕ) / 2]'(by grind) : Tensor ℝ [])
      set s : Tensor ℝ [] := (θ.sin[(j : ℕ) / 2]'(by grind) : Tensor ℝ [])
      set xj : Tensor ℝ [] := id (α := Tensor ℝ []) (x[j])
      set xj1 : Tensor ℝ [] := id (α := Tensor ℝ []) (x[j1])
      have hj_entry : θ.rotaryMatrix'[j][j] = c := by
        unfold c
        simpa [hj] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj1_entry : θ.rotaryMatrix'[j1][j] = s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j1 j
        have hodd : ¬((j1 : ℕ) % 2 = 0) := by simp [j1]; omega
        have hne : (j : ℕ) ≠ (j1 : ℕ) := by simp [j1]
        have heq : (j : ℕ) + 1 = (j1 : ℕ) := by simp [j1]
        simp [hodd, hne, heq] at hk
        let i1 : Fin d := ⟨(j1 : ℕ) / 2, by
          have : (j1 : ℕ) < d + d := j1.isLt
          simp [j1] at this ⊢; omega⟩
        let i0 : Fin d := ⟨(j : ℕ) / 2, by grind⟩
        have hi : i1 = i0 := Fin.ext (by simp [i1, i0, j1]; omega)
        exact (congrArg (fun i : Fin d => (θ.sin[i] : Tensor ℝ [])) hi) ▸ hk
      rw [hj_entry, hj1_entry]
      change Add.add (c * xj) (s * xj1) = _
      have h' : Add.add (c * xj) (s * xj1) = Add.add (xj * c) (xj1 * s) := by
        congr 1
        · exact Tensor.Mul.hComm c xj
        · exact Tensor.Mul.hComm s xj1
      refine h'.trans ?_
      simp [xj, xj1, c, s, j1, id_eq, Tensor.Add]
  · let j0 : Fin (d + d) := ⟨(j : ℕ) - 1, by omega⟩
    have hj0ne : j0 ≠ j := Fin.ne_of_val_ne (by simp [j0]; omega)
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[k][j]) *
            id (α := Tensor ℝ []) (x[k]))
        j0 j (Finset.mem_univ _) (Finset.mem_univ _) hj0ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hneJ : (k : ℕ) ≠ (j : ℕ) := Fin.val_ne_iff.mpr hk1
      have hneJ0 : ¬((k : ℕ) + 1 = (j : ℕ)) := by
        intro h; exact hk0 (Fin.ext (by simp [j0]; omega))
      have hk' :
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[k][j]) =
            id (α := Tensor ℝ []) (0 : Tensor ℝ []) := by
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ k j
        by_cases hk_even : (k : ℕ) % 2 = 0
        · simp only [hk_even, ↓reduceIte] at hk
          have hjk : (j : ℕ) ≠ (k : ℕ) := Ne.symm hneJ
          have hjk1 : (j : ℕ) ≠ (k : ℕ) + 1 := by
            intro h; exact hneJ0 (by omega)
          simpa [hjk, hjk1, id] using hk
        · simp only [hk_even, ↓reduceIte] at hk
          have hjk : (j : ℕ) ≠ (k : ℕ) := Ne.symm hneJ
          have hjk1 : (j : ℕ) + 1 ≠ (k : ℕ) := by
            intro h; omega
          simpa [hjk, hjk1, id] using hk
      rw [hk']
      simp only [id_eq]
      rw [Tensor.Mul]
      exact zero_mul _
    · set c : Tensor ℝ [] := (θ.cos[(j : ℕ) / 2]'(by grind) : Tensor ℝ [])
      set s : Tensor ℝ [] := (θ.sin[(j : ℕ) / 2]'(by grind) : Tensor ℝ [])
      set xj : Tensor ℝ [] := id (α := Tensor ℝ []) (x[j])
      set xj0 : Tensor ℝ [] := id (α := Tensor ℝ []) (x[j0])
      have hj_entry : θ.rotaryMatrix'[j][j] = c := by
        unfold c
        have hodd : ¬((j : ℕ) % 2 = 0) := hj
        simpa [hodd] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj0_entry : θ.rotaryMatrix'[j0][j] = -s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j0 j
        have heven : (j0 : ℕ) % 2 = 0 := by simp [j0]; omega
        have heq : (j : ℕ) = (j0 : ℕ) + 1 := by simp [j0]; omega
        simp [heven, heq] at hk
        let i0' : Fin d := ⟨(j0 : ℕ) / 2, by
          have : (j0 : ℕ) < d + d := j0.isLt
          simp [j0] at this ⊢; omega⟩
        let i0 : Fin d := ⟨(j : ℕ) / 2, by grind⟩
        have hi : i0' = i0 := Fin.ext (by simp [i0', i0, j0]; omega)
        exact (congrArg (fun i : Fin d => (-(θ.sin[i] : Tensor ℝ []) : Tensor ℝ [])) hi) ▸ hk
      rw [hj0_entry, hj_entry]
      change Add.add ((-s) * xj0) (c * xj) = _
      have h := Tensor.AddMulS.eq.SubMulS c s xj xj0
      have h' : Add.add ((-s) * xj0) (c * xj) = xj * c - xj0 * s := by
        rw [show Add.add ((-s) * xj0) (c * xj) = Add.add (c * xj) ((-s) * xj0) from add_comm _ _]
        exact h
      refine h'.trans ?_
      simp [xj, xj0, c, s, j0, id_eq]


-- created on 2026-09-16
