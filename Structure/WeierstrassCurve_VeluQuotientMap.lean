import Mathlib
import Structure.WeierstrassCurve_Velu
import Def.WeierstrassCurve_VeluQuotientMap

open Polynomial

namespace WeierstrassCurve

variable {R : Type*} [CommRing R] (W : WeierstrassCurve R)

structure IsOddVeluSet (S : Finset (R × R)) : Prop where

  equation : ∀ P ∈ S, W.toAffine.Equation P.1 P.2

  gy_ne_zero : ∀ P ∈ S, W.veluGy P.1 P.2 ≠ 0

  x_injOn : ∀ P ∈ S, ∀ P' ∈ S, P.1 = P'.1 → P = P'


section QuotientMap

variable {F : Type*} [Field F] (W : WeierstrassCurve F)


end QuotientMap


end WeierstrassCurve
