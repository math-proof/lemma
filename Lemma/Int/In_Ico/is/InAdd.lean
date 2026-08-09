import Lemma.Int.EqSubAdd
import Lemma.Int.LeSubS.is.Le
import Lemma.Int.LtSubS.is.Lt
import Lemma.Set.InAdd.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
open Int Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Ico.is.InAdd |
| comm | Int.InAdd.is.In_Ico |
| mp | Int.InAdd.of.In_Ico |
| mpr | Int.In_Ico.of.InAdd |
| mp.mt | Int.NotIn_Ico.of.NotInAdd |
| mpr.mt | Int.NotInAdd.of.NotIn_Ico |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α] [Preorder α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
-- given
  (x a b t : α) :
-- imply
  x ∈ Ico a b ↔ x + t ∈ Ico (a + t) (b + t) := by
-- proof
  constructor
  · intro h
    exact InAdd.of.In_Ico h t
  · intro h
    let ⟨h₀, h₁⟩ := Le.Lt.of.In_Ico h
    have h₀ := GeSubS.of.Ge t h₀
    have h₁ := LtSubS.of.Lt t h₁
    repeat rw [EqSubAdd] at h₀ h₁
    exact In_Ico.of.Le.Lt h₀ h₁


-- created on 2026-08-08
