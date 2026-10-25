import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Abbrev.Analysis.Section_6_1.Part12


namespace Chapter6

/-- Definition 6.1.8 (Convergent, def) -/
theorem Sequence.convergent_def (a:Sequence) : a.Convergent ↔ ∃ L, a.TendsTo L := by rfl

end Chapter6
