import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Abbrev.Analysis.Section_6_1.Part16


namespace Chapter6

/-- Definition 6.1.16 (IsBounded, def) -/
lemma Sequence.isBounded_def (a:Sequence) :
  a.IsBounded ↔ ∃ M ≥ 0, a.BoundedBy M := by rfl

end Chapter6
