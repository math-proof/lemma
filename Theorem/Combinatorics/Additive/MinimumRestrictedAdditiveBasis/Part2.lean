/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
import Mathlib.Data.Finset.Card
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Nat.Find
import Mathlib.Data.Finset.Range
import Mathlib.Tactic
import Def.Combinatorics.Additive.MinimumRestrictedAdditiveBasis


namespace MetaMathlibExt

/-- The value of `minimumRestrictedAdditiveBasisCard s` is `none` iff `s % 2 = 1`. -/
theorem minimumRestrictedAdditiveBasisCard_eq_none_iff (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val = none ↔ s % 2 = 1 := by
  rw [← Nat.odd_iff]
  constructor
  · intro hnone
    have hno := (minimumRestrictedAdditiveBasisCard s).property.2 hnone
    have hEven : ¬Even s := fun hev => hno (mrab_exists_of_even s hev)
    rwa [Nat.not_even_iff_odd] at hEven
  · intro hodd
    have hno := mrab_not_exists_of_odd hodd
    cases hval : (minimumRestrictedAdditiveBasisCard s).val with
    | none => rfl
    | some k =>
      have hex := ((minimumRestrictedAdditiveBasisCard s).property.1 k hval).1
      obtain ⟨A, hP, hQ, -⟩ := hex
      exact absurd ⟨A, hP, hQ⟩ hno

/-- The value of `minimumRestrictedAdditiveBasisCard s` is `some` iff `s % 2 = 0`. -/
theorem minimumRestrictedAdditiveBasisCard_isSome_iff (s : ℕ) :
    (minimumRestrictedAdditiveBasisCard s).val.isSome ↔ s % 2 = 0 := by
  rw [← Nat.even_iff]
  rw [Option.isSome_iff_exists]
  constructor
  · rintro ⟨k, hk⟩
    have hex := ((minimumRestrictedAdditiveBasisCard s).property.1 k hk).1
    obtain ⟨A, hP, hQ, -⟩ := hex
    have hno : ¬Odd s :=
      fun hodd => (mrab_not_exists_of_odd hodd) ⟨A, hP, hQ⟩
    rwa [Nat.not_odd_iff_even] at hno
  · intro hev
    have hne : (minimumRestrictedAdditiveBasisCard s).val ≠ none := by
      intro hnone
      have hno := (minimumRestrictedAdditiveBasisCard s).property.2 hnone
      exact hno (mrab_exists_of_even s hev)
    exact Option.ne_none_iff_exists'.mp hne

end MetaMathlibExt
