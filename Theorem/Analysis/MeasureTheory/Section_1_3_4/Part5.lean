import Theorem.Analysis.MeasureTheory.Section_1_3_3.Part2
import Instance.Analysis.MeasureTheory.Section_1_3_4.Part2


theorem PreL1.dist_eq {d:ℕ} (F G: PreL1 d) : dist F G = ‖F-G‖ :=
  dist_eq_norm F G

