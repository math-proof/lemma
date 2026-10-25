import Mathlib
import Class.Patching_SystemTypes

set_option autoImplicit false

variable (R : Type*) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

class IsProartinian : Prop extends IsLinearTopology R R, T0Space R,
    letI := IsTopologicalAddGroup.rightUniformSpace R; CompleteSpace R where
  isArtinianRing_quotient (I : Ideal R) : IsOpen (X := R) I → IsArtinianRing (R ⧸ I)

attribute [instance low] IsProartinian.toIsLinearTopology
  IsProartinian.toT0Space IsProartinian.toCompleteSpace
