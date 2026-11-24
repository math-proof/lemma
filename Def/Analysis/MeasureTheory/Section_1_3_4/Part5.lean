module
public import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
public import Instance.Analysis.MeasureTheory.Section_1_3_4.Part3


public section

noncomputable def ComplexAbsolutelyIntegrable.toL1 {d:ℕ} {f:EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : L1 d := SeparationQuotient.mk hf.to_PreL1

