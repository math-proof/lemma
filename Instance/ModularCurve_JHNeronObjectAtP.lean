module
public import Mathlib
public import Def.ModularCurve_JZeroNeronObjectAtP
public import Abbrev.GoodReductionJacobian_RelativeGroupLawBaseChange
public import Theorem.Scheme.NeronSpecialFibreRestriction
public import Instance.ModularCurve_XHDifferentialsModL
public import Theorem.UpperHalfPlane.XHOperators
public import Theorem.ResidueField.GluedPic0
public import Def.GaloisRep_Flat
public import Def.FLTPrelim_Ramification
public import Def.ModularCurve_JHNeronObjectAtP
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra GoodReductionJacobian
open ModularCurve.JZeroNeronObjectAtP
open scoped MatrixGroups


public section

-- Carved from Lemma/Definitions/Def_ModularCurve_JHNeronObjectAtP.lean: instance decls only.

noncomputable section

namespace ModularCurve


namespace JHNeronObjectAtP

variable {p M : ℕ} [Fact p.Prime] [NeZero M] {H : Subgroup (ZMod M)ˣ} {hpM : p ∣ M}

instance (O : JHNeronObjectAtP p M H hpM A hA Λ) : AddCommGroup O.Pts := O.pts.symm.addCommGroup

end JHNeronObjectAtP

end ModularCurve

end
