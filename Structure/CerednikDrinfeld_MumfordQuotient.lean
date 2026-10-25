import Mathlib.FieldTheory.Fixed
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Localization.Basic
import Mathlib.Algebra.Ring.Action.Group
import Lemma.Scheme.AlgebraicCurveBaseChangeGalois
import Def.CerednikDrinfeld_MumfordVertexType
import Instance.CerednikDrinfeld_MumfordQuotient

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld.Mumford

section Generic

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]


structure AmbientSemilinearAut where

  base : K ≃+* K

  map : M ≃+* M
  map_algebraMap : ∀ c : K, map (algebraMap K M c) = algebraMap K M (base c)
  map_smul : ∀ (g : G) (m : M), map (g • m) = g • map m

namespace AmbientSemilinearAut

variable {K G M}

section Transport

omit [SMulCommClass G K M]


end Transport

section Coeff


end Coeff

end AmbientSemilinearAut

end Generic

section MumfordLayer

variable (K : Type) [Field K] (G : Type) [Group G] (M : Type) [CommRing M] [IsDomain M] [Algebra K M]
variable [MulSemiringAction G M] [SMulCommClass G K M]


variable {W : Type} [MulAction G W] (𝒯 : SimpleGraph W) (w₀ : W)


end MumfordLayer

end CerednikDrinfeld.Mumford

end
