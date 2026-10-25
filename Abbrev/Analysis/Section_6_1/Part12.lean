import Mathlib
import Theorem.Analysis.Section_5_1.Part9
import Theorem.Analysis.Section_5_3.Part12
import Theorem.Analysis.Section_5_epilogue.Part5
import Theorem.Analysis.Section_6_1.Part11


namespace Chapter6

/-- Definition 6.1.8 (Convergent) -/
abbrev Sequence.Convergent (a:Sequence) : Prop := ∃ L, a.TendsTo L

end Chapter6
