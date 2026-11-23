module

public import Mathlib

public section


public theorem Filter.cofinite.sets.countable (ι : Type*) [Countable ι] :
  (Filter.cofinite : Filter ι).sets.Countable :=
  Set.Countable.mono (fun _ h ↦ h) <|
    Set.Countable.preimage_of_injOn Set.Countable.ofPred_finite compl_bijective.1.injOn

