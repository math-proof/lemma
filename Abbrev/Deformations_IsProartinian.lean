import Mathlib
import Class.Patching_SystemTypes
import Instance.Deformations_Deformations_Lemmas
import Class.Deformations_IsProartinian

set_option autoImplicit false

namespace AdicTopologyAux

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≥ ·)]
variable (α : ι → Type*) (f : ∀ i j, i ≤ j → α i → α j)
variable [∀ i, TopologicalSpace (α i)]
variable (hf : ∀ i j h, Continuous (f i j h))

end AdicTopologyAux

section AdicTopology

variable (R : Type*) [CommRing R] [IsLocalRing R] [TopologicalSpace R] [IsTopologicalRing R]

namespace IsLocalRing

variable [IsAdicTopology R]

abbrev withIdeal {R} [CommRing R] [IsLocalRing R] : WithIdeal R := ⟨maximalIdeal R⟩

attribute [local instance] withIdeal

end IsLocalRing

end AdicTopology

section Proartinian

variable {R S : Type*} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]
  [CommRing S] [TopologicalSpace S] [IsTopologicalRing S]

section IsLocalRing

open IsLocalRing

variable [IsLocalRing R] [IsLocalRing S]

end IsLocalRing

end Proartinian
