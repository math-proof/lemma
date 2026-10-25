-- Carved from Lemma/Definitions/Def_ModularCurve_JHNeronObjectAtP.lean: instance decls only.
import Mathlib
import Def.ModularCurve_JZeroNeronObjectAtP
import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
import Lemma.AlgebraicGeometry.NeronSpecialFibreRestriction
import Instance.ModularCurve_XHDifferentialsModL
import Lemma.ModularCurve.XHOperators
import Lemma.AlgebraicCurve.GluedPic0
import Def.GaloisRep_Flat
import Def.FLTPrelim_Ramification
import Def.ModularCurve_JHNeronObjectAtP

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups

noncomputable section

namespace ModularCurve


namespace JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

instance (O : JHNeronObjectAtP p M H hpM A hA Λ) : AddCommGroup O.Pts := O.pts.symm.addCommGroup

end JHNeronObjectAtP

end ModularCurve

end
