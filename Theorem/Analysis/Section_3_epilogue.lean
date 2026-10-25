import Mathlib
import Mathlib.SetTheory.ZFC.PSet
import Mathlib.SetTheory.ZFC.Basic
import Theorem.Analysis.Tools.ExistsUnique.Part2
import Abbrev.Analysis.Section_3_1_api
set_option doc.verso.suggestions false
set_option backward.isDefEq.respectTransparency false

universe u

/-!
# Analysis I, Chapter 3 epilogue: Connections with ZFSet

In this epilogue we show that the {name}`ZFSet` type in Mathlib (derived as a quotient from the
{name}`PSet` type) can be used to create models of the `SetTheory` class studied in this chapter, so long as we work in a universe of level at
least 1.  The constructions here are due to Edward van de Meent; see
https://leanprover.zulipchat.com/#narrow/channel/113489-new-members/topic/Can.20this.20proof.20related.20to.20Set.20replacement.20be.20shorter.3F/near/527305173
-/


/-- A preliminary lemma about `PSet`: their natural numbers are ordered by membership. -/
lemma PSet.ofNat_mem_ofNat_of_lt (m n : ℕ) : n < m → ofNat n ∈ ofNat m := by
  intro h
  induction h with
  | refl => rw [ofNat]; apply mem_insert
  | step _ ih => rw [ofNat]; exact mem_insert_of_mem _ ih

lemma PSet.mem_ofNat_iff (n m : ℕ) : ofNat n ∈ ofNat m ↔ n < m := by
  refine ⟨ ?_, ofNat_mem_ofNat_of_lt m n ⟩
  contrapose!; rw [le_iff_lt_or_eq]; rintro (h|rfl)
  · exact mem_asymm (ofNat_mem_ofNat_of_lt _ _ h)
  apply mem_irrefl

/-- Another preliminary lemma: Natural numbers in {name}`PSet` can only be equivalent
if they are equal. -/
lemma PSet.eq_of_ofNat_equiv_ofNat (n m : ℕ): (ofNat.{u} n).Equiv (ofNat.{u} m) → n = m := by
  wlog hmn : m ≤ n generalizing n m
  · intro heq; rw [this _ _ _ heq.symm]; order
  intro h; rw [Equiv.eq, Set.ext_iff] at h
  have : n ≤ m := by specialize h (ofNat m); simpa [mem_irrefl, mem_ofNat_iff] using h
  order

