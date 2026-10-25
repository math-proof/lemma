import Mathlib
import Lemma.ModularCurve.HeckeModule
import Def.ModularCurve_HeckeInputsAll
import Def.FLTPrelim_Ramification
import Lemma.ModularCurve.ToricMonodromyPart
import Def.GaloisRep_Flat
import Structure.ModularCurve_JZeroNeronData

set_option autoImplicit false
noncomputable section

namespace ModularCurve

open ValuationSubring

section JZeroNeronAux
variable (M : ℕ) [NeZero M]


end JZeroNeronAux


def HasJZeroNeronData (N q : ℕ) [NeZero N] [Fact q.Prime] (hqN : ¬ q ∣ N) : Prop :=
  ∀ (A : ValuationSubring (AlgebraicClosure ℚ)) (hA : A.LiesOverPrime q), Nonempty (JZeroNeronData N q hqN A hA)

end ModularCurve

end
