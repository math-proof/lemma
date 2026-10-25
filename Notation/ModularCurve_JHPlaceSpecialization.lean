set_option quotPrecheck false
set_option hygiene false

/-!
# Notations from `Lemma/Definitions/Def_ModularCurve_JHPlaceSpecialization.lean`

Scoped so the same token can denote a different expression in another file.
The right-hand side resolves where the notation is used.
-/

namespace ModularCurve_JHPlaceSpecialization

scoped notation "κ" => ResidueField ↥A

scoped notation "FM" => ↥(xHFunctionFieldBar M H)

scoped notation "FMp" => ↥(xHFunctionFieldBar (M / p) (ModularCurve.infSubgroup p M H hpM))

scoped notation "Fb" => JHNeronObjectAtP.Fbar p M H hpM (ResidueField ↥A)

scoped notation "Γ′" => ModularCurve.JHNeronObjectAtP.ΓN p M H hpM

end ModularCurve_JHPlaceSpecialization
