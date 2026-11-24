module
public import Mathlib
public import Theorem.Analysis.Section_5_1.Part9
public import Theorem.Analysis.Section_5_3.Part12
public import Theorem.Analysis.Section_5_epilogue.Part5
public import Theorem.Analysis.Section_6_1.Part11


public section

namespace Chapter6

/-- Definition 6.1.8 (Convergent) -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

end Chapter6
