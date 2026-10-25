import Def.Analysis.MeasureTheory.Notation.Part2
import Theorem.Analysis.Section_9_1.Part3
import Abbrev.Analysis.MeasureTheory.Section_1_1_1
open BoundedInterval


/-- Any nonempty {name}`BoundedInterval` has a ≤ b -/
lemma BoundedInterval.nonempty_implies_le (I : BoundedInterval) (h : I.toSet.Nonempty) : I.a ≤ I.b := by
  cases I with
  | Ioo a b => exact le_of_lt (nonempty_Ioo_strictness h)
  | Icc a b => exact nonempty_Icc_order h
  | Ioc a b => exact le_of_lt (nonempty_Ioc_strictness h)
  | Ico a b => exact le_of_lt (nonempty_Ico_strictness h)

/-- Any bounded interval is contained in the closed interval with the same endpoints. -/
theorem BoundedInterval.subset_Icc (I: BoundedInterval) : I ⊆ Icc I.a I.b := match I with
  | Ioo _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Icc _ _ => by simp [subset_iff]
  | Ioc _ _ => by simp [subset_iff, Set.Ioc_subset_Icc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ico_subset_Icc_self]

/-- The open interval with the same endpoints is contained in any bounded interval. -/
theorem BoundedInterval.Ioo_subset (I: BoundedInterval) : Ioo I.a I.b ⊆ I := match I with
  | Ioo _ _ => by simp [subset_iff]
  | Icc _ _ => by simp [subset_iff, Set.Ioo_subset_Icc_self]
  | Ioc _ _ => by simp [subset_iff, Set.Ioo_subset_Ioc_self]
  | Ico _ _ => by simp [subset_iff, Set.Ioo_subset_Ico_self]

