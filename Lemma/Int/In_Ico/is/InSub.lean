import Lemma.Int.EqAddSub
import Lemma.Int.LeSubS.is.Le
import Lemma.Int.LtSubS.is.Lt
import Lemma.Set.InAdd.of.In_Ico
import Lemma.Set.In_Ico.is.Le.Lt
open Int Set


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Ico.is.InSub |
| comm | Int.InSub.is.In_Ico |
| mp | Int.InSub.of.In_Ico |
| mpr | Int.In_Ico.of.InSub |
| mp.mt | Int.NotIn_Ico.of.NotInSub |
| mpr.mt | Int.NotInSub.of.NotIn_Ico |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α]
  [Preorder α]
  [AddLeftMono α] [AddRightMono α]
  [AddLeftStrictMono α] [AddRightStrictMono α]
-- given
  (x a b d : α) :
-- imply
  x ∈ Ico a b ↔ x - d ∈ Ico (a - d) (b - d) := by
-- proof
  constructor
  · intro h
    let ⟨h₀, h₁⟩ := Le.Lt.of.In_Ico h
    have h₀ := LeSubS.of.Le d h₀
    have h₁ := LtSubS.of.Lt d h₁
    exact In_Ico.of.Le.Lt h₀ h₁
  · intro h
    have h := InAdd.of.In_Ico h d
    simpa [EqAddSub] using h


-- created on 2026-08-08
