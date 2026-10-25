import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Abbrev.Analysis.MeasureTheory.Section_1_3_4


@[coe]
noncomputable def PreL1.toL1 {d:ℕ} (F: PreL1 d) : L1 d := SeparationQuotient.mk F

