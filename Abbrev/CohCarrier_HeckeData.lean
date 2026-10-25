import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w


namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)

abbrev FreeAlg : Type u := MvPolynomial D.Gen 𝒪

end HeckeData

end CohCarrier

end
