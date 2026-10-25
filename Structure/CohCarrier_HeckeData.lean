import Mathlib.Algebra.Module.LocalizedModule.Basic
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.Algebra.Algebra.Subalgebra.Lattice
import Instance.CohCarrier_HeckeData

set_option autoImplicit false

noncomputable section

namespace CohCarrier

universe u v w

structure HeckeData (𝒪 : Type u) [CommRing 𝒪] (V : Type v) [AddCommGroup V] [Module 𝒪 V]
    (k : Type w) [Field k] [Algebra 𝒪 k] where

  Gen : Type

  op : Gen → Module.End 𝒪 V

  comm : ∀ g h : Gen, op g * op h = op h * op g

  θbar : Gen → k

namespace HeckeData

variable {𝒪 : Type u} [CommRing 𝒪] {V : Type v} [AddCommGroup V] [Module 𝒪 V]
  {k : Type w} [Field k] [Algebra 𝒪 k] (D : HeckeData 𝒪 V k)


open scoped IsMulCommutative


end HeckeData

end CohCarrier

end
