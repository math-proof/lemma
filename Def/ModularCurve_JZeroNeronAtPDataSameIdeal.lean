module

public import Mathlib
public import Structure.ModularCurve_JZeroNeronAtPDataSameIdeal

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace ModularCurve


def HasJZeroNeronAtPDataSameIdeal (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataSameIdeal N q hqN A hA)

end ModularCurve

end
