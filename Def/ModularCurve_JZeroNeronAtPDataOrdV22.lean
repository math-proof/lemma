module

public import Mathlib
public import Def.ModularCurve_JZeroNeronAtPDataOrdCore
public import Structure.ModularCurve_JZeroNeronAtPDataOrdV22

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve


def HasJZeroNeronAtPDataOrdV22 (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdV22 N q hqN A hA)

end ModularCurve

end
