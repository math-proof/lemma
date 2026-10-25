-- Carved from Lemma/Definitions/Def_Gamma0CoeffCohomologyEigen.lean: instance decls only.
import Mathlib
import Instance.Gamma0CoeffCohomology
import Lemma.HeckeEis.BinaryFormRep
import Lemma.Gamma0CoeffCohomologyEigen.Main

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

section H1

variable {G : Type*} [Group G] {K : Type*} [CommRing K] {V : Type*} [AddCommGroup V] [Module K V]

instance instAddCommGroupCoeffH1 (ρ : Representation K G V) : AddCommGroup (coeffH1 ρ) :=
  inferInstanceAs (AddCommGroup
    (↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype))

instance instModuleCoeffH1 (ρ : Representation K G V) : Module K (coeffH1 ρ) :=
  inferInstanceAs (Module K
    (↥(coeffCocycles ρ) ⧸ (coeffCoboundaries ρ).comap (coeffCocycles ρ).subtype))

end H1


end HeckeEis
