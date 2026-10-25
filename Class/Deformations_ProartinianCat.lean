import Mathlib
import Class.Deformations_IsProartinian
import Class.Deformations_IsResidueAlgebra

set_option autoImplicit false

open IsLocalRing

universe u

variable {𝓞 : Type*} [CommRing 𝓞]

class IsLocalProartinianAlgebra
    (R : Type u) [CommRing R] [TopologicalSpace R] [Algebra 𝓞 R] : Prop extends
  IsTopologicalRing R, IsLocalRing R, IsProartinian R,
  IsLocalHom (algebraMap 𝓞 R), IsResidueAlgebra 𝓞 R
