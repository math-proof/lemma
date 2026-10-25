import Mathlib
import Def.AutomorphicForm_HeckeEigensystem
import Def.LanglandsTunnell_ExplicitLift
import Structure.LanglandsTunnell_OctahedralDatum

set_option autoImplicit false

open AutomorphicForm IsDedekindDomain NumberField
open scoped MatrixGroups

namespace FLT.TunnellOctahedralGlobalCarrier


def TunnellOctahedralGlobal {R : Type*} [CommRing R] (notion : CuspidalityNotion R) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∀ D : OctahedralGaloisDatum F R,
      ∃ π : HeckeEigensystem F R,
        notion.IsCusp F π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

end FLT.TunnellOctahedralGlobalCarrier

namespace FLT.Qepw139bOctahedralDatumLinkedRecarve

open FLT.TunnellOctahedralGlobalCarrier


def TunnellOctahedralGlobalLinked {R : Type*} [CommRing R]
    (notion : CuspidalityNotion R) : Prop :=
  ∀ (F : Type) [Field F] [NumberField F],
    ∀ D : OctahedralGaloisDatumLinked F R,
      ∃ π : HeckeEigensystem F R,
        notion.IsCusp F π ∧ HeckeEigensystem.AgreesAwayFromFinite π D.attached

end FLT.Qepw139bOctahedralDatumLinkedRecarve
