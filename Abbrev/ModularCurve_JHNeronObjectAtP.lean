import Mathlib
import Structure.ModularCurve_JZeroNeronObjectAtP
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Def.AlgebraicGeometry_NeronSpecialFibreRestriction
import Instance.ModularCurve_XHDifferentialsModL
import Def.ModularCurve_XHOperators
import Abbrev.AlgebraicCurve_GluedPic0
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
  AlgebraicCurve IsLocalRing
open ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

noncomputable section

namespace ModularCurve

namespace JHNeronObjectAtP

abbrev ΓN (p M : ℕ) (H : Subgroup (ZMod M)ˣ) (hpM : p ∣ M) : Subgroup SL(2, ℤ) :=
  CohCarrier.GammaH (M / p) (infSubgroup p M H hpM)


end JHNeronObjectAtP

open JHNeronObjectAtP in


namespace JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}
  {A : ValuationSubring (AlgebraicClosure ℚ)} {hA : A.LiesOverPrime p}
  [CharP (ResidueField ↥A) p] [IsAlgClosed (ResidueField ↥A)]
  {Λ : LevelData p M H hpM A}

end JHNeronObjectAtP

end ModularCurve

end
