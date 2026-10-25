/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Range
import Mathlib.Tactic


namespace MetaMathlibExt

theorem mrab_exists_of_even (s : Nat) (hs : Even s) :
    ∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  obtain ⟨r, rfl⟩ := hs
  refine ⟨Finset.range (r + 1), ?_, ?_⟩
  · intro a ha
    rw [Finset.mem_range] at ha
    omega
  · intro x hx
    refine ⟨min x r, Finset.mem_range.mpr (by omega), x - min x r,
      Finset.mem_range.mpr (by omega), ?_⟩
    have hle : min x r ≤ x := Nat.min_le_left x r
    omega

theorem mrab_not_exists_of_odd {s : Nat} (hs : Odd s) :
    ¬∃ A : Finset Nat, (∀ a ∈ A, 2 * a ≤ s) ∧
      ∀ x : Nat, x ≤ s → ∃ a ∈ A, ∃ b ∈ A, a + b = x := by
  rintro ⟨A, hbound, hcover⟩
  obtain ⟨a, haA, b, hbA, hab⟩ := hcover s le_rfl
  have ha := hbound a haA
  have hb := hbound b hbA
  rw [Nat.odd_iff] at hs
  omega

end MetaMathlibExt
