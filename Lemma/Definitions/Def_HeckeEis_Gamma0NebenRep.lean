import Mathlib

set_option autoImplicit false

namespace HeckeEis

open CongruenceSubgroup
open scoped MatrixGroups

noncomputable def gamma0NebenChar (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Gamma0 M →* κ :=
  (powMonoidHom e).comp
    ((ZMod.castHom (dvd_refl p) κ).toMonoidHom.comp
      ((ZMod.castHom hpM (ZMod p)).toMonoidHom.comp (Gamma0Map M)))

theorem gamma0NebenChar_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) :
    gamma0NebenChar p M hpM κ e γ =
      (ZMod.castHom (dvd_refl p) κ (ZMod.castHom hpM (ZMod p) (((γ : SL(2, ℤ)) 1 1 : ℤ) : ZMod M))) ^ e :=
  rfl

noncomputable def gamma0NebenRep (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Representation κ (Gamma0 M) κ :=
  (DistribMulAction.toModuleEnd κ κ).comp (gamma0NebenChar p M hpM κ e)

@[simp]
theorem gamma0NebenRep_apply (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ)
    (γ : Gamma0 M) (v : κ) :
    gamma0NebenRep p M hpM κ e γ v = gamma0NebenChar p M hpM κ e γ * v :=
  rfl

theorem gamma0NebenRep_zero (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] :
    gamma0NebenRep p M hpM κ 0 = 1 := by
  refine MonoidHom.ext fun γ => LinearMap.ext fun v => ?_
  simp [gamma0NebenChar]

end HeckeEis
