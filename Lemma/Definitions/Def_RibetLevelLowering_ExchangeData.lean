import Mathlib

open Module

namespace RibetEndgame

structure ExchangeData (k : Type) [Field k] : Type 1 where

  Xp : Type
  [acgXp : AddCommGroup Xp]
  [modXp : Module k Xp]
  [finXp : Module.Finite k Xp]

  Yq : Type
  [acgYq : AddCommGroup Yq]
  [modYq : Module k Yq]
  [finYq : Module.Finite k Yq]

  Lp : Type
  [acgLp : AddCommGroup Lp]
  [modLp : Module k Lp]
  [finLp : Module.Finite k Lp]

  Yp : Type
  [acgYp : AddCommGroup Yp]
  [modYp : Module k Yp]
  [finYp : Module.Finite k Yp]

  Lq : Type
  [acgLq : AddCommGroup Lq]
  [modLq : Module k Lq]
  [finLq : Module.Finite k Lq]

  f : Yq →ₗ[k] Lp

  g : Lp →ₗ[k] Xp

  surj_g : Function.Surjective g

  exact_fg : LinearMap.ker g ≤ LinearMap.range f

  lam : ℕ

  mu : ℕ

  finrank_Yp : finrank k Yp = 2 * mu

  finrank_Lp : finrank k Lp = 2 * lam

  finrank_Yq_le : finrank k Yq ≤ mu

  finrank_Lq_le : finrank k Lq ≤ lam

  finrank_Xp_le : finrank k Xp ≤ mu

  lam_pos : 0 < lam

attribute [instance] ExchangeData.acgXp ExchangeData.modXp ExchangeData.finXp
attribute [instance] ExchangeData.acgYq ExchangeData.modYq ExchangeData.finYq
attribute [instance] ExchangeData.acgLp ExchangeData.modLp ExchangeData.finLp
attribute [instance] ExchangeData.acgYp ExchangeData.modYp ExchangeData.finYp
attribute [instance] ExchangeData.acgLq ExchangeData.modLq ExchangeData.finLq

namespace ExchangeData

variable {k : Type} [Field k]

def SeqIso (d : ExchangeData k) : Prop :=
  finrank k d.Yp = finrank k d.Lq

end ExchangeData

end RibetEndgame
