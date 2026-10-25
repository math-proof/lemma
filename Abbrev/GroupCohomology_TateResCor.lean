import Mathlib
import Abbrev.GroupCohomology_TateCohomology

set_option autoImplicit false

universe u v w

open CategoryTheory

namespace Representation

namespace TateResCor

variable {G : Type v} [Group G] (S : Subgroup G)

section coinvariants

variable {k : Type u} {V : Type w} [CommRing k] [AddCommGroup V] [Module k V] (ρ : Representation k G V)

end coinvariants

section maps

variable {k : Type u} {G : Type v} {V : Type w} [CommRing k] [Group G] [AddCommGroup V] [Module k V]
  (ρ : Representation k G V) (S : Subgroup G)

end maps

end TateResCor

end Representation

namespace Rep

open Representation.TateResCor

variable {k : Type u} {G : Type v} [CommRing k] [Group G] [Fintype G] (S : Subgroup G) [Fintype S] (A : Rep.{w} k G)

noncomputable abbrev tateH0Res : A.tateH0 →ₗ[k] (Rep.res S.subtype A).tateH0 :=
  Representation.TateResCor.tateH0Res A.ρ S

noncomputable abbrev tateH0Cores : (Rep.res S.subtype A).tateH0 →ₗ[k] A.tateH0 :=
  Representation.TateResCor.tateH0Cores A.ρ S

noncomputable abbrev tateHneg1Res : A.tateHneg1 →ₗ[k] (Rep.res S.subtype A).tateHneg1 :=
  Representation.TateResCor.tateHneg1Res A.ρ S

noncomputable abbrev tateHneg1Cores : (Rep.res S.subtype A).tateHneg1 →ₗ[k] A.tateHneg1 :=
  Representation.TateResCor.tateHneg1Cores A.ρ S

end Rep
