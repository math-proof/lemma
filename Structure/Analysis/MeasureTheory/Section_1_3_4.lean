module

public import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
public import Theorem.Analysis.MeasureTheory.Section_1_3_4.Part2


public section

@[ext]
structure PreL1 (d:ℕ) where
  f : EuclideanSpace' d → ℂ
  integrable : ComplexAbsolutelyIntegrable f

