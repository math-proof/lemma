module

public import Mathlib
public import Def.ModularCurve_JZeroNeronAtPDataSameIdeal
public import Structure.ModularCurve_JZeroNeronAtPDataOrdCore

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve


def HasJZeroNeronAtPDataOrdCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdCore N q hqN A hA)

end ModularCurve

end
