import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Def.Analysis.MeasureTheory.Section_1_3_4.Part4


noncomputable instance PreL1.inst_coeL1 {d:ℕ} : Coe (PreL1 d) (L1 d) := ⟨ PreL1.toL1 ⟩

