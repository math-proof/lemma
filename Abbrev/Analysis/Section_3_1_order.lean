module

public import Instance.Analysis.Section_3_1.Part5
public import Theorem.Set.Subset.of.Subset.Subset_SetTheory_Set_subset_trans

@[expose] public section


namespace Chapter3

universe u v

variable [SetTheory]

open SetTheory

open SetTheory.Set

abbrev SetTheory.Set.subset_trans {A B C:Set} (hAB:A ⊆ B) (hBC:B ⊆ C) : A ⊆ C :=
  _root_.Set.Subset.of.Subset.Subset_SetTheory_Set_subset_trans (A := A) (B := B) (C := C) (hAB := hAB) (hBC := hBC)

end Chapter3
