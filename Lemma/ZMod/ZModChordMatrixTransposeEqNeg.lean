import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false


variable {N : ℕ} [NeZero N]
private lemma val_sub_cases
  {a b : ZMod N} (hab : a ≠ b) :
  (a - b).val = if b.val ≤ a.val then a.val - b.val else N + a.val - b.val := by
  cases le_or_gt b.val a.val
  ·
    rename_i h
    simp only [h, ite_true, ZMod.val_sub h]
  ·
    rename_i h
    simp only [not_le.mpr h, ite_false]
    have hba : b - a ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    have hrw : a - b = -(b - a) := by
      ring
    rw [hrw, ZMod.neg_val, ite_eq_right hba, ZMod.val_sub (le_of_lt h)]
    have hal : a.val < N := ZMod.val_lt _
    omega
private def σ
  (a b k : ZMod N) :
  ℤ :=
  if k ≠ a ∧ (k - a).val < (b - a).val then 1 else 0
private lemma σ_shift
  (a b k c : ZMod N) :
  σ (a + c) (b + c) (k + c) = σ a b k := by
  unfold σ
  congr 1
  simp only [ne_eq, add_right_cancel_iff, add_sub_add_right_eq_sub]
private lemma σ_sub
  (a b k : ZMod N) :
  σ a b k = σ 0 (b - a) (k - a) := by
  have this := σ_shift (N := N) 0 (b - a) (k - a) a
  simp only [zero_add, sub_add_cancel] at this
  refine this
private lemma σ_antisymm_four
  {x y z w : ZMod N}
  (hxy : x ≠ y) (hxz : x ≠ z) (hxw : x ≠ w)
  (hyz : y ≠ z) (hyw : y ≠ w) (hzw : z ≠ w) :
  σ x y z - σ x y w + σ z w x - σ z w y = 0 := by
  rw [σ_sub x y z, σ_sub x y w, σ_sub z w x, σ_sub z w y]
  set Y := y - x with hYdef
  set Z := z - x with hZdef
  set W := w - x with hWdef
  have hY : Y ≠ 0 := sub_ne_zero.mpr (Ne.symm hxy)
  have hZ : Z ≠ 0 := sub_ne_zero.mpr (Ne.symm hxz)
  have hW : W ≠ 0 := sub_ne_zero.mpr (Ne.symm hxw)
  have hYZ : Y ≠ Z := by
    intro h
    rw [hYdef, hZdef] at h
    refine hyz (sub_left_injective h)
  have hYW : Y ≠ W := by
    intro h
    rw [hYdef, hWdef] at h
    refine hyw (sub_left_injective h)
  have hZW : Z ≠ W := by
    intro h
    rw [hZdef, hWdef] at h
    refine hzw (sub_left_injective h)
  have hwz : w - z = W - Z := by
    rw [hWdef, hZdef]
    ring
  have hxz' : x - z = -Z := by
    rw [hZdef]
    ring
  have hyz' : y - z = Y - Z := by
    rw [hYdef, hZdef]
    ring
  rw [hwz, hxz', hyz']
  unfold σ
  simp only [ne_eq, hZ, not_false_eq_true, true_and, hW, sub_zero,
    neg_eq_zero, sub_eq_zero]
  have hYZ' : ¬(Y = Z) := hYZ
  simp only [hYZ', not_false_eq_true, true_and]
  rw [ZMod.neg_val, ite_eq_right hZ,
    val_sub_cases (a := W) (b := Z) hZW.symm,
    val_sub_cases (a := Y) (b := Z) hYZ]
  have hYlt := ZMod.val_lt Y
  have hZlt := ZMod.val_lt Z
  have hWlt := ZMod.val_lt W
  have hY1 : 1 ≤ Y.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero Y).not.mpr hY)
  have hZ1 : 1 ≤ Z.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero Z).not.mpr hZ)
  have hW1 : 1 ≤ W.val := Nat.one_le_iff_ne_zero.mpr ((ZMod.val_eq_zero W).not.mpr hW)
  have hYZv : Y.val ≠ Z.val := fun h => hYZ (ZMod.val_injective _ h)
  have hYWv : Y.val ≠ W.val := fun h => hYW (ZMod.val_injective _ h)
  have hZWv : Z.val ≠ W.val := fun h => hZW (ZMod.val_injective _ h)
  split_ifs
  all_goals omega
/--
[ZMod_chordMatrix_transpose_eq_neg](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ZMod_chordMatrix_transpose_eq_neg.lean)
-/
@[path]
private lemma main
  {m : ℕ} [NeZero m]
  (a b : Fin m → ZMod (2 * m))
  (hdist : Function.Injective (fun p : Fin m × Bool => cond p.2 (a p.1) (b p.1))) :
  -- imply
  let P : Matrix (Fin m) (Fin m) ℤ := fun i j =>
    (if a j ≠ a i ∧ (a j - a i).val < (b i - a i).val then (1 : ℤ) else 0) -
    (if b j ≠ a i ∧ (b j - a i).val < (b i - a i).val then (1 : ℤ) else 0)
  P.transpose = -P := by
  -- proof
  intro P
  let _ : NeZero (2 * m) := ⟨Nat.mul_ne_zero two_ne_zero (NeZero.ne m)⟩
  have hd : ∀ (p q : Fin m × Bool), p ≠ q →
      cond p.2 (a p.1) (b p.1) ≠ cond q.2 (a q.1) (b q.1) :=
    fun p q h heq => h (hdist heq)
  have haa : ∀ i j, i ≠ j → a i ≠ a j := fun i j h =>
    hd (i, true) (j, true) (by simp [h])
  have hab : ∀ i j, a i ≠ b j := fun i j =>
    hd (i, true) (j, false) (by simp)
  have hbb : ∀ i j, i ≠ j → b i ≠ b j := fun i j h =>
    hd (i, false) (j, false) (by simp [h])
  funext i j
  simp only [Matrix.transpose_apply, Matrix.neg_apply, P]
  if hij : i = j then
    subst hij
    simp only [ne_eq, not_true_eq_false, false_and, ite_false, sub_self,
      lt_irrefl, and_false, neg_zero]
  else
    have key : σ (a i) (b i) (a j) - σ (a i) (b i) (b j) +
        σ (a j) (b j) (a i) - σ (a j) (b j) (b i) = 0 :=
      σ_antisymm_four (N := 2 * m) (hab i i) (haa i j hij) (hab i j)
        (hab j i).symm (hbb i j hij) (hab j j)
    unfold σ at key
    linarith


-- created on 2026-10-21
