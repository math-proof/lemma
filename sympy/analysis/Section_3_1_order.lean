import sympy.analysis.Section_3_1
import Lemma.Set.Subset.of.Subset.Subset_SetTheory_Set_subset_trans

namespace Chapter3

universe u v

variable [SetTheory]

open SetTheory
open SetTheory.Set

abbrev SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C :=
  _root_.Set.Subset.of.Subset.Subset_SetTheory_Set_subset_trans (A := A) (B := B) (C := C) (hAB := hAB) (hBC := hBC)

/-- Not from textbook: sets form a distributive lattice. -/
instance SetTheory.Set.instDistribLattice : DistribLattice Set where
  le := (· ⊆ ·)
  le_refl := subset_self
  le_trans := fun _ _ _ ↦ subset_trans
  le_antisymm := subset_antisymm
  inf := (· ∩ ·)
  sup := (· ∪ ·)
  le_sup_left := by sorry
  le_sup_right := by sorry
  sup_le := by sorry
  inf_le_left := by sorry
  inf_le_right := by sorry
  le_inf := by sorry
  le_sup_inf := by
    intro X Y Z; change (X ∪ Y) ∩ (X ∪ Z) ⊆ X ∪ (Y ∩ Z)
    rw [←union_inter_distrib_left]

/-- Sets have a minimal element. -/
instance SetTheory.Set.instOrderBot : OrderBot Set where
  bot := ∅
  bot_le := empty_subset

end Chapter3
