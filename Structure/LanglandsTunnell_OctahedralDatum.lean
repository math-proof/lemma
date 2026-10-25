import Mathlib
import Structure.AutomorphicForm_HeckeEigensystem
import Def.LanglandsTunnell_ExplicitLift

set_option autoImplicit false

open AutomorphicForm IsDedekindDomain NumberField
open scoped MatrixGroups

namespace FLT.TunnellOctahedralGlobalCarrier

structure OctahedralGaloisDatum (F : Type) [Field F] [NumberField F]
    (R : Type*) [CommRing R] where

  G : Type

  [grp : Group G]

  [fin : Finite G]

  proj : G →* Equiv.Perm (Fin 4)

  proj_surjective : Function.Surjective proj

  attached : HeckeEigensystem F R

attribute [instance] OctahedralGaloisDatum.grp OctahedralGaloisDatum.fin


end FLT.TunnellOctahedralGlobalCarrier

namespace FLT.Qepw139bOctahedralDatumLinkedRecarve

open FLT.TunnellOctahedralGlobalCarrier

structure OctahedralGaloisDatumLinked (F : Type) [Field F] [NumberField F]
    (R : Type*) [CommRing R] extends OctahedralGaloisDatum F R where

  rep : G →* GL (Fin 2) R

  rep_proj : ∀ g : G, proj g = 1 ↔
    ∃ c : Rˣ, ((rep g : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R) = (c : R) • 1

  frob : HeightOneSpectrum (𝓞 F) → G

  ramified : Finset (HeightOneSpectrum (𝓞 F))

  attached_a : ∀ v ∉ ramified,
    attached.a v = ((rep (frob v) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).trace

  attached_b : ∀ v ∉ ramified,
    attached.b v = ((rep (frob v) : GL (Fin 2) R) : Matrix (Fin 2) (Fin 2) R).det


end FLT.Qepw139bOctahedralDatumLinkedRecarve
