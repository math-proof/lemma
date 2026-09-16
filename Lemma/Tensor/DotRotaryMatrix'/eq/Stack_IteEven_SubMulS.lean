import Lemma.Tensor.Add
import Lemma.Tensor.DataAdd.eq.AddDataS
import Lemma.Tensor.DataNeg.eq.NegData
import Lemma.Tensor.Dot.eq.Stack_Sum_MulGetS
import Lemma.Tensor.Eq.is.All_EqGetS
import Lemma.Tensor.Eq.is.EqDataS
import Lemma.Tensor.EqGetStack
import Lemma.Tensor.GetRotaryMatrix'.eq.Ite_IteS
import Lemma.Tensor.Mul
import Lemma.Tensor.NegMul.eq.MulNeg
import Lemma.Vector.GetAdd.eq.AddGetS
import Lemma.Vector.GetNeg.eq.NegGet
import Lemma.Vector.GetSub.eq.SubGet
import torch.functions
import torch.stack
open Nat Tensor Fin
set_option maxHeartbeats 4000000


private lemma tensor_nil_sub_eq_add_add
    (X Y : Tensor ℝ []) : X - Y = Add.add X (-Y) := by
  apply Eq.of.EqDataS
  ext i
  have hi : (i : ℕ) = 0 := Nat.lt_one_iff.mp i.isLt
  change (X.data - Y.data[0]).get i = (Add.add X (-Y)).data.get i
  erw [Vector.GetSub.eq.SubGet.fin (x := X.data) (a := Y.data[0]) (i := i)]
  erw [DataAdd.eq.AddDataS X (-Y)]
  erw [DataNeg.eq.NegData Y]
  erw [Vector.GetAdd.eq.AddGetS.fin (a := X.data) (b := -Y.data) (i := i)]
  erw [Vector.GetNeg.eq.NegGet.fin (x := Y.data) (i := i)]
  rw [sub_eq_add_neg (X.data.get i) (Y.data[0])]
  apply congrArg (fun t => X.data.get i + -t)
  apply congrArg Y.data.get
  apply Fin.ext
  simp [hi]

private lemma tensor_nil_mul_comm
    (X Y : Tensor ℝ []) : X * Y = Y * X := by
  rw [Tensor.Mul, Tensor.Mul (X := Y) (Y := X)]
  exact mul_comm X Y

private lemma tensor_nil_even_rope
    (c s x0 x1 : Tensor ℝ []) :
    Add.add (c * x0) ((-s) * x1) = x0 * c - x1 * s := by
  have h : c * x0 + -s * x1 = x0 * c - x1 * s := by
    rw [tensor_nil_sub_eq_add_add, Tensor.Add]
    congr 1
    · exact tensor_nil_mul_comm c x0
    · have h1 : (-s) * x1 = -(s * x1) := (NegMul.eq.MulNeg.nil s x1).symm
      have h2 : s * x1 = x1 * s := tensor_nil_mul_comm s x1
      rw [h1, h2]
  rwa [Tensor.Add] at h

private lemma tensor_nil_odd_rope
    (c s x0 x1 : Tensor ℝ []) :
    Add.add (s * x1) (c * x0) = Add.add (x0 * c) (x1 * s) := by
  have h : s * x1 + c * x0 = x0 * c + x1 * s := by
    rw [Tensor.Add, Tensor.Add (X := x0 * c) (Y := x1 * s)]
    rw [show Add.add (s * x1) (c * x0) = Add.add (c * x0) (s * x1) from add_comm _ _]
    congr 1
    · exact tensor_nil_mul_comm c x0
    · exact tensor_nil_mul_comm s x1
  rwa [Tensor.Add, Tensor.Add (X := x0 * c) (Y := x1 * s)] at h


@[main]
private lemma main
-- given
  (θ : Tensor ℝ [d])
  (x : Tensor ℝ [d + d]) :
-- imply
  θ.rotaryMatrix' @ x =
    [j < d + d]
      if h : (j : ℕ) % 2 = 0 then
        let j1 : Fin (d + d) := ⟨(j : ℕ) + 1, by omega⟩
        id (α := Tensor ℝ []) (x[j]) *
            id (α := Tensor ℝ []) (θ.cos[(j : ℕ) / 2]'(by grind)) -
          id (α := Tensor ℝ []) (x[j1]) *
            id (α := Tensor ℝ []) (θ.sin[(j : ℕ) / 2]'(by grind))
      else
        let j0 : Fin (d + d) := ⟨(j : ℕ) - 1, by omega⟩
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
    let j1 : Fin (d + d) := ⟨(j : ℕ) + 1, by omega⟩
    have hj1ne : j ≠ j1 := Fin.ne_of_val_ne (by simp [j1])
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) *
            id (α := Tensor ℝ []) (x[k]))
        j j1 (Finset.mem_univ _) (Finset.mem_univ _) hj1ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hk := GetRotaryMatrix'.eq.Ite_IteS θ j k
      simp only [hj, ↓reduceIte] at hk
      have hne0 : (k : ℕ) ≠ (j : ℕ) := Fin.val_ne_iff.mpr hk0
      have hne1 : (k : ℕ) ≠ (j : ℕ) + 1 := by
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
        simpa [hj] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj1_entry : θ.rotaryMatrix'[j][j1] = -s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j j1
        have heq : (j1 : ℕ) = (j : ℕ) + 1 := by simp [j1]
        have hne : (j1 : ℕ) ≠ (j : ℕ) := by simp [j1]
        simp [hj, heq] at hk
        exact hk
      rw [hj_entry, hj1_entry]
      change Add.add (c * xj) ((-s) * xj1) = _
      refine (tensor_nil_even_rope c s xj xj1).trans ?_
      simp [xj, xj1, c, s, j1, id_eq]
  · -- odd column
    let j0 : Fin (d + d) := ⟨(j : ℕ) - 1, by omega⟩
    have hj0ne : j0 ≠ j := Fin.ne_of_val_ne (by simp [j0]; omega)
    refine (Finset.sum_eq_add_of_mem (s := (Finset.univ : Finset (Fin (d + d))))
        (f := fun k =>
          id (α := Tensor ℝ []) (θ.rotaryMatrix'[j][k]) *
            id (α := Tensor ℝ []) (x[k]))
        j0 j (Finset.mem_univ _) (Finset.mem_univ _) hj0ne ?_).trans ?_
    · intro k _ ⟨hk0, hk1⟩
      have hk := GetRotaryMatrix'.eq.Ite_IteS θ j k
      have hodd : ¬((j : ℕ) % 2 = 0) := hj
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
        have hodd : ¬((j : ℕ) % 2 = 0) := hj
        simpa [hodd] using GetRotaryMatrix'.eq.Ite_IteS θ j j
      have hj0_entry : θ.rotaryMatrix'[j][j0] = s := by
        unfold s
        have hk := GetRotaryMatrix'.eq.Ite_IteS θ j j0
        have hodd : ¬((j : ℕ) % 2 = 0) := hj
        have hne : (j0 : ℕ) ≠ (j : ℕ) := by simp [j0]; omega
        have heq : (j0 : ℕ) + 1 = (j : ℕ) := by simp [j0]; omega
        simp [hodd, hne, heq] at hk
        exact hk
      rw [hj_entry, hj0_entry]
      change Add.add (s * xj0) (c * xj) = _
      refine (tensor_nil_odd_rope c s xj xj0).trans ?_
      · symm
        change _ = Add.add (xj * c) (xj0 * s)
        simp [xj, xj0, c, s, j0, id_eq, Tensor.Add]


-- created on 2026-09-16
-- updated on 2026-09-16
