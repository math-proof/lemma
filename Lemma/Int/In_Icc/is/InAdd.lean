import Lemma.Set.In_Icc.is.Le.Le
import Lemma.Nat.LeAddS.is.Le
import Lemma.Int.LeSubS.is.Le
import Lemma.Int.EqSubAdd
open Set Nat Int


/--
| attributes | lemma |
| :---: | :---: |
| main | Int.In_Icc.is.InAdd |
| comm | Int.InAdd.is.In_Icc |
| mp | Int.InAdd.of.In_Icc |
| mpr | Int.In_Icc.of.InAdd |
| mp.mt | Int.NotIn_Icc.of.NotInAdd |
| mpr.mt | Int.NotInAdd.of.NotIn_Icc |
-/
@[main, comm, mp, mpr, mp.mt, mpr.mt]
private lemma main
  [AddGroup α] [Preorder α]
  [AddLeftMono α] [AddRightMono α]
-- given
  (x a b t : α) :
-- imply
  x ∈ Icc a b ↔ x + t ∈ Icc (a + t) (b + t) := by
-- proof
  constructor <;>
    intro h
  ·
    -- requires [Add α]
    let ⟨h₀, h₁⟩ := Le.Le.of.In_Icc h
    have h₀ := GeAddS.of.Ge t h₀
    have h₁ := LeAddS.of.Le t h₁
    apply In_Icc.of.Le.Le h₀ h₁
  ·
    -- requires [AddGroup α]
    let ⟨h₀, h₁⟩ := Le.Le.of.In_Icc h
    have h₀ := GeSubS.of.Ge t h₀
    have h₁ := GeSubS.of.Ge t h₁
    repeat rw [EqSubAdd] at h₀ h₁
    apply In_Icc.of.Le.Le h₀ h₁


-- created on 2020-02-27
-- updated on 2025-05-12
