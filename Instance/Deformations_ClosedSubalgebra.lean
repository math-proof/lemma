-- Carved from Lemma/Definitions/Def_Deformations_ClosedSubalgebra.lean: instance decls only.
import Mathlib
import Lemma.Deformations.TraceAlgebra
import Instance.Deformations_ProartinianCompact
import Lemma.Deformations.ClosedSubalgebra

set_option autoImplicit false

universe u

open CategoryTheory Function Limits IsLocalRing Filter Topology

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞] [IsLocalRing 𝓞]

namespace ProartinianCat

variable {A : ProartinianCat 𝓞}


section ClosedSubalgebraObj

variable [CompactSpace A.carrier] (S : Subalgebra 𝓞 A.carrier) (hS : IsClosed (S : Set A.carrier))

namespace ClosedSubalgebra

instance : Nontrivial S :=
  ⟨0, 1, fun h => zero_ne_one (α := A.carrier) (congrArg (fun z : S => (z : A.carrier)) h)⟩

instance : IsTopologicalRing S := S.toSubring.instIsTopologicalRing

instance : IsLinearTopology S S := .mk_of_hasBasis _ (hasBasis_nhds_zero S)

end ClosedSubalgebra

end ClosedSubalgebraObj

end ProartinianCat


end Deformation
