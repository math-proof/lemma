module
public import Mathlib
public import Theorem.MvPolynomial.HeckeModule
public import Def.ModularCurve_HeckeInputsAll
public import Def.FLTPrelim_Ramification
public import Theorem.Submodule.ToricMonodromyPart
public import Def.GaloisRep_Flat
public import Structure.ModularCurve_JZeroNeronData
set_option autoImplicit false


public section

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
