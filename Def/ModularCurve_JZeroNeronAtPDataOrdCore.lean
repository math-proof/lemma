import Mathlib
import Def.ModularCurve_JZeroNeronAtPDataSameIdeal
import Structure.ModularCurve_JZeroNeronAtPDataOrdCore

set_option autoImplicit false

noncomputable section

namespace ModularCurve


def HasJZeroNeronAtPDataOrdCore (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronAtPDataOrdCore N q hqN A hA)

end ModularCurve

end
