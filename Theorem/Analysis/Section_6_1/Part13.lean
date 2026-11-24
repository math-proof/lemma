module
public import Mathlib
public import Theorem.Analysis.Section_5_1.Part9
public import Theorem.Analysis.Section_5_3.Part12
public import Theorem.Analysis.Section_5_epilogue.Part5
public import Abbrev.Analysis.Section_6_1.Part13


public section

namespace Chapter6

/-- Definition 6.1.8 (Divergent, def) -/
theorem Sequence.divergent_def (a:Sequence) : a.Divergent ↔ ¬ a.Convergent := by rfl

end Chapter6
