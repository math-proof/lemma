/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/PadicNumbers.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Order.DirectedInverseSystem
import Mathlib.Data.ZMod.Basic
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.RingTheory.Ideal.Quotient.Operations
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib
import Theorem.v1.Atlas.ArithmeticGeometry.code.PadicNumbers.Part2


namespace DiscreteValuation

variable {R : Type*} [CommRing R] (v : DiscreteValuation R)

/-- Forward map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
sends $x \in \mathbb{Z}_p$ to the compatible sequence of its reductions modulo $p^n$. -/
def padicIntToInvLim : ℤ_[p] →+* (zmodInvLimSubring p) where
  toFun x := ⟨fun n => toZModPow n x, fun m n h =>
    RingHom.congr_fun (PadicInt.zmod_cast_comp_toZModPow m n h) x⟩
  map_one' := Subtype.ext (funext fun _ => map_one _)
  map_mul' x y := Subtype.ext (funext fun _ => map_mul _ x y)
  map_add' x y := Subtype.ext (funext fun _ => map_add _ x y)
  map_zero' := Subtype.ext (funext fun _ => map_zero _)

/-- Inverse map of the isomorphism $\mathbb{Z}_p \simeq \varprojlim \mathbb{Z}/p^n\mathbb{Z}$:
obtained via the universal property `PadicInt.lift` from the family of compatible projections. -/
def invLimToPadicInt : (zmodInvLimSubring p) →+* ℤ_[p] :=
  PadicInt.lift (invLimProj_compat p)

/-- Theorem 4.6 (inverse-limit description): the ring isomorphism $\mathbb{Z}_p \simeq
\varprojlim_n \mathbb{Z}/p^n\mathbb{Z}$. -/
def padicIntEquivInvLim : ℤ_[p] ≃+* (zmodInvLimSubring p) :=
  RingEquiv.ofRingHom
    (padicIntToInvLim p)
    (invLimToPadicInt p)
    (RingHom.ext fun a => by
      ext n
      simp only [padicIntToInvLim, RingHom.coe_mk, MonoidHom.coe_mk, OneHom.coe_mk,
        RingHom.comp_apply, RingHom.id_apply]
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) = (a : ∀ n, ZMod (p ^ n)) n
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) a) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) a from rfl,
        PadicInt.lift_spec]
      rfl)
    (RingHom.ext fun x => by
      simp only [RingHom.comp_apply, RingHom.id_apply]
      apply PadicInt.ext_of_toZModPow.mp
      intro n
      change (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) = _
      rw [show (toZModPow n) (PadicInt.lift (invLimProj_compat p) (padicIntToInvLim p x)) =
        ((toZModPow n).comp (PadicInt.lift (invLimProj_compat p))) (padicIntToInvLim p x) from rfl,
        PadicInt.lift_spec]
      simp [invLimProj, padicIntToInvLim])

end DiscreteValuation
