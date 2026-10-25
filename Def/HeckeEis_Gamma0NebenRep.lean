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


noncomputable def gamma0NebenRep (p M : ℕ) (hpM : p ∣ M) (κ : Type*) [CommRing κ] [CharP κ p] (e : ℕ) :
    Representation κ (Gamma0 M) κ :=
  (DistribMulAction.toModuleEnd κ κ).comp (gamma0NebenChar p M hpM κ e)

end HeckeEis
