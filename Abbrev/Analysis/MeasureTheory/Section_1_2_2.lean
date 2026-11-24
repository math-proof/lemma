module
public import Theorem.Analysis.MeasureTheory.Section_1_2_1.Part15
public import Theorem.Analysis.MeasureTheory.Section_1_2_2


public section

abbrev IsNull {d:ℕ} (E: Set (EuclideanSpace' d)) : Prop := Lebesgue_outer_measure E = 0

