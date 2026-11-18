module

public import Mathlib
public import Abbrev.Analysis.Section_5_2
@[expose] public section

namespace Chapter5

abbrev Sequence.Equiv (a b: ℕ → ℚ) : Prop :=
  ∀ ε > (0:ℚ), ε.EventuallyClose (Sequence.ofNatFun a) (Sequence.ofNatFun b)

end Chapter5
