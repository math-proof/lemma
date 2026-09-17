import Lemma.Nat.Even.is.Mod_2.eq.Zero
import Lemma.Tensor.Add
import Lemma.Tensor.AddMulS.eq.SubMulS
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetRotaryMatrix'.eq.Ite_IteS
import Lemma.Tensor.Mul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Tensor.Sub.eq.Add_Neg
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSub.eq.SubGet
import torch.functions
import torch.stack
import sympy.functions.elementary.integers
open Tensor
set_option maxHeartbeats 4000000


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (x : Tensor ℝ [d + d]) :
-- imply
  θ.rotaryMatrix' @ x =
    [j < d + d]
      if h : (j : ℕ) is even then
        let j1 : Fin (d + d) := ⟨j + 1, by grind⟩
        id (α := Tensor ℝ []) (x[j]) *
            id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(by grind)) -
          id (α := Tensor ℝ []) (x[j1]) *
            id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(by grind))
      else
        let j0 : Fin (d + d) := ⟨j - 1, by omega⟩
        id (α := Tensor ℝ []) (x[j]) *
            id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(by grind)) +
          id (α := Tensor ℝ []) (x[j0]) *
            id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(by grind)) := by
-- proof
  apply Eq.trans (Dot.eq.Stack_Sum_MulGetS.mv θ.rotaryMatrix' x)
  apply Tensor.Eq.of.All_EqGetS.fin
  intro j
  conv_lhs => erw [EqGetStack.fin (i := j)]
  conv_rhs => erw [EqGetStack.fin (i := j)]
  split_ifs with hj
  · -- even column
    have hj_mod : (j : ℕ) % 2 = 0 := Nat.Mod_2.eq.Zero.of.Even hj
    let j1 : Fin (d + d) := ⟨j + 1, by omega⟩
    have hj1ne : j ≠ j1 := Fin.ne_of_val_ne (by simp [j1])
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) *
            id (α := Tensor ℝ []) (x[k]))
        j j1 (Finset.mem_univ _) (Finset.mem_univ _) hj1ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hk := GetRotaryMatrix'.eq.Ite_IteS θ j k
      simp only [hj_mod, ↓reduceIte] at hk
      have hne0 : (k : ℕ) ≠ (j : ℕ) := Fin.val_ne_iff.mpr hk0
      have hne1 : (k : ℕ) ≠ j + 1 := by
        intro h; exact hk1 (Fin.ext (by simpa [j1] using h))
      have hk' :
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) =
            id (α := Tensor ℝ []) (0 : Tensor ℝ []) := by
        simpa [hne0, hne1, id] using hk
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
        simpa [hj_mod] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj1_entry : θ.rotaryMatrix'[j][j1] = -s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j j1
        have heq : (j1 : ℕ) = j + 1 := by simp [j1]
        have hne : (j1 : ℕ) ≠ (j : ℕ) := by simp [j1]
        simp [hj_mod, heq] at hk
        exact hk
      rw [hj_entry, hj1_entry]
      change Add.add (c * xj) ((-s) * xj1) = _
      refine (Tensor.AddMulS.eq.SubMulS c s xj xj1).trans ?_
      simp [xj, xj1, c, s, j1, id_eq]
  · -- odd column
    have hodd : ¬((j : ℕ) % 2 = 0) := fun h => hj (Nat.Even.of.Mod_2.eq.Zero h)
    let j0 : Fin (d + d) := ⟨j - 1, by omega⟩
    have hj0ne : j0 ≠ j := Fin.ne_of_val_ne (by simp [j0]; omega)
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) *
            id (α := Tensor ℝ []) (x[k]))
        j0 j (Finset.mem_univ _) (Finset.mem_univ _) hj0ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hk := GetRotaryMatrix'.eq.Ite_IteS θ j k
      simp only [hodd, ↓reduceIte] at hk
      have hneJ : (k : ℕ) ≠ (j : ℕ) := Fin.val_ne_iff.mpr hk1
      have hneJ0 : ¬((k : ℕ) + 1 = (j : ℕ)) := by
        intro h; exact hk0 (Fin.ext (by simp [j0]; omega))
      have hk' :
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) =
            id (α := Tensor ℝ []) (0 : Tensor ℝ []) := by
        simpa [hneJ, hneJ0, id] using hk
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
        simpa [hodd] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj0_entry : θ.rotaryMatrix'[j][j0] = s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j j0
        have hne : (j0 : ℕ) ≠ (j : ℕ) := by simp [j0]; omega
        have heq : (j0 : ℕ) + 1 = (j : ℕ) := by simp [j0]; omega
        simp [hodd, hne, heq] at hk
        exact hk
      rw [hj_entry, hj0_entry]
      change Add.add (s * xj0) (c * xj) = _
      have h_swap : Add.add (s * xj0) (c * xj) = Add.add (c * xj) (s * xj0) :=
        Eq.symm (add_comm _ _)
      rw [h_swap]
      have h_comm := Tensor.Mul.hComm c xj
      have h_comm' := Tensor.Mul.hComm s xj0
      rw [h_comm, h_comm']
      unfold xj0 j0
      simp only [Tensor.Add, id_eq]


-- created on 2023-05-22
-- updated on 2026-09-16
