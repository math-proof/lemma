module

public import Mathlib
public import Abbrev.Analysis.MeasureTheory.Notation.Part2

@[expose] public section

instance EuclideanSpace'.inst_coeReal : Coe ℝ (EuclideanSpace' 1) := ⟨Real.equiv_EuclideanSpace'⟩

