module

public import Mathlib
public import Instance.Analysis.MeasureTheory.Notation

@[expose] public section


abbrev EuclideanSpace'.toReal (x: EuclideanSpace' 1) : ℝ := EuclideanSpace'.equiv_Real x

abbrev Real.toEuclideanSpace' (x: ℝ) : EuclideanSpace' 1 := Real.equiv_EuclideanSpace' x

