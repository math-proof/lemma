module

public import Mathlib
public import Structure.Dieudonne_DatumAndHonda

@[expose] public section

set_option autoImplicit false

open LinearMap Submodule Function

universe u v

namespace Deformation

variable {𝓞 : Type u} [CommRing 𝓞]


namespace DieudonneDatum

variable {ℓ : 𝓞} {D : Type v} [AddCommGroup D] [Module 𝓞 D] (M : DieudonneDatum ℓ D)

def IsEtaleType : Prop := Function.Bijective M.F

def IsMultiplicativeType : Prop := Function.Bijective M.V

def IsLocalLocal : Prop := M.F = 0 ∧ M.V = 0

variable (ℓ) in

def etaleOne : DieudonneDatum ℓ 𝓞 where
  F := LinearMap.id
  V := ℓ • LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

variable (ℓ) in

def multOne : DieudonneDatum ℓ 𝓞 where
  F := ℓ • LinearMap.id
  V := LinearMap.id
  fv := by ext; simp
  vf := by ext; simp

end DieudonneDatum


end Deformation

end
