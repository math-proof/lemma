import Def.ModularCurve_ComponentGroupHecke
import Structure.HeckeGalois_EichlerShimura
import Structure.CerednikDrinfeld_Ribbon

set_option autoImplicit false

noncomputable section

namespace ModularCurve


end ModularCurve

namespace CerednikDrinfeld

open ModularCurve

variable {E V : Type*} [Fintype E] [Fintype V] [DecidableEq V] {D : DegeneracyData E V}


namespace HeckeData

variable (H : HeckeData D)

structure LatticeHyp (H : HeckeData D) where

  n : Nat.Primes → ℤ

  colSum : ∀ ℓ, HeckeRowSums (H.T ℓ).transpose (n ℓ)

  nV : Nat.Primes → ℤ

  colSumV : ∀ ℓ, HeckeRowSums (H.Tv ℓ).transpose (nV ℓ)

variable (h : H.LatticeHyp)


end HeckeData

end CerednikDrinfeld
