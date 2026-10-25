import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Instance.Analysis.MeasureTheory.Section_1_3_4.Part3


noncomputable def ComplexAbsolutelyIntegrable.toL1 {d:ℕ} {f:EuclideanSpace' d → ℂ} (hf: ComplexAbsolutelyIntegrable f) : L1 d := SeparationQuotient.mk hf.to_PreL1

