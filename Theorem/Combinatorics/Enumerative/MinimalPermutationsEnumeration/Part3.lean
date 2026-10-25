/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MinimalPermutationsEnumeration.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.GroupTheory.Perm.Fin
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Order.Interval.Finset.Fin
import Mathlib.Data.Fin.Rev
import Mathlib.Order.Fin.Basic
import Def.Combinatorics.Enumerative.MinimalPermutationsEnumeration.Part2


section

namespace MetaMathlibExt

theorem block1Pos_val (d : ℕ) (a : Fin (d + 1)) (i : Fin (a.val + 1)) :
    (block1Pos d a i).val = i.val := rfl

theorem block2Pos_val (d : ℕ) (a : Fin (d + 1))
    (i : Fin ((d - a.val) + 1)) :
    (block2Pos d a i).val = a.val + 1 + i.val := rfl

theorem block1_anti (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    StrictAnti (fun i : Fin (a.val + 1) => σ (block1Pos d a i)) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have hi : i.val < a.val := i.isLt
  have hlt : i.val < d + 1 := by
    have ha2 := a.isLt
    omega
  let k : Fin (d + 1) := ⟨i.val, hlt⟩
  have hk : k.val = i.val := rfl
  have hkne : k ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    simp only [hk] at hv
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  have e1 : block1Pos d a i.castSucc = k.castSucc := by
    apply Fin.ext
    simp only [block1Pos_val, Fin.val_castSucc, hk]
  have e2 : block1Pos d a i.succ = k.succ := by
    apply Fin.ext
    simp only [block1Pos_val, Fin.val_succ, hk]
  simp only [e1, e2]
  exact hdesc

theorem block2_anti (d : ℕ) (σ : Equiv.Perm (Fin (d + 2))) (a : Fin (d + 1))
    (ha : (Finset.univ.filter fun i : Fin (d + 1) =>
      σ i.castSucc < σ i.succ) = {a}) :
    StrictAnti (fun i : Fin ((d - a.val) + 1) => σ (block2Pos d a i)) := by
  rw [Fin.strictAnti_iff_succ_lt]
  intro i
  have hi : i.val < d - a.val := i.isLt
  have ha2 := a.isLt
  have hlt : a.val + 1 + i.val < d + 1 := by omega
  let k : Fin (d + 1) := ⟨a.val + 1 + i.val, hlt⟩
  have hk : k.val = a.val + 1 + i.val := rfl
  have hkne : k ≠ a := by
    intro he
    have hv := congrArg Fin.val he
    simp only [hk] at hv
    omega
  have hdesc := descent_of_ne_ascent d σ a k ha hkne
  have e1 : block2Pos d a i.castSucc = k.castSucc := by
    apply Fin.ext
    simp only [block2Pos_val, Fin.val_castSucc, hk]
  have e2 : block2Pos d a i.succ = k.succ := by
    apply Fin.ext
    simp only [block2Pos_val, Fin.val_succ, hk]
    have h1 : (i.succ).val = i.val + 1 := Fin.val_succ i
    have h2 : (i.castSucc).val = i.val := Fin.val_castSucc i
    omega
  simp only [e1, e2]
  exact hdesc

end MetaMathlibExt
end
