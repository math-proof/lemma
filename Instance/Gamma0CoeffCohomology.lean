-- Carved from Lemma/Definitions/Def_Gamma0CoeffCohomology.lean: instance decls only.
import Mathlib
import Instance.Gamma0HeckeOperatorHom
import Lemma.Gamma0CoeffCohomology.Main

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups


section Parabolic

variable {Γ : Subgroup SL(2, ℤ)} {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

instance instAddCommGroupCoeffH1par (ρ : Representation K Γ V) : AddCommGroup (coeffH1par ρ) :=
  inferInstanceAs (AddCommGroup
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

instance instModuleCoeffH1par (ρ : Representation K Γ V) : Module K (coeffH1par ρ) :=
  inferInstanceAs (Module K
    (↥(coeffParabolicCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffParabolicCocycles ρ).subtype))

end Parabolic


end HeckeEis
