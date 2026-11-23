module

public import Mathlib
public import Def.Matrix_TraceAlgebra
public import Instance.Deformations_ProartinianCompact
public import Instance.Deformations_ClosedSubalgebra

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing Filter Topology

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat

variable {A : ProartinianCat 𝓞}

omit [IsLocalRing 𝓞] in


section ClosedSubalgebraObj

variable [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))

namespace ClosedSubalgebra

include hS in

include hS in

end ClosedSubalgebra

noncomputable def closedSubalgebraObj : ProartinianCat 𝓞 :=
  letI := ClosedSubalgebra.isLocalProartinianAlgebra S hS
  of 𝓞 S

noncomputable def closedSubalgebraι : closedSubalgebraObj S hS ⟶ A :=
  letI := ClosedSubalgebra.isLocalProartinianAlgebra S hS
  ofHom ⟨S.val, continuous_subtype_val⟩

end ClosedSubalgebraObj

end ProartinianCat

section Universal

open ProartinianCat

variable {n : Type} [Fintype n] [DecidableEq n]
variable {G : Type u} [Group G] [TopologicalSpace G]

namespace TraceAlgebra

variable [Finite (ResidueField 𝓞)] {A : ProartinianCat 𝓞}

noncomputable def obj (ρ : G →ₜ* GL n A) : ProartinianCat 𝓞 :=
  closedSubalgebraObj (traceSubalgebra 𝓞 ρ) (isClosed_traceSubalgebra ρ)

noncomputable def ι (ρ : G →ₜ* GL n A) : obj ρ ⟶ A :=
  closedSubalgebraι (traceSubalgebra 𝓞 ρ) (isClosed_traceSubalgebra ρ)

end TraceAlgebra

end Universal

end Deformation

end
