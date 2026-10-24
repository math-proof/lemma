import Mathlib

set_option autoImplicit false

universe u

namespace ModularCurve

noncomputable section

abbrev uvCrossingIdeal (W : Type u) [CommRing W] (π : W) : Ideal (MvPowerSeries (Fin 2) W) :=
  Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
    MvPowerSeries.C π}

abbrev UVCrossingModel (W : Type u) [CommRing W] (π : W) : Type u :=
  MvPowerSeries (Fin 2) W ⧸ uvCrossingIdeal W π

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

def mk (π : W) : MvPowerSeries (Fin 2) W →+* UVCrossingModel W π :=
  Ideal.Quotient.mk _

def U (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 0)

def V (π : W) : UVCrossingModel W π := mk π (MvPowerSeries.X 1)

def const (π : W) (w : W) : UVCrossingModel W π := mk π (MvPowerSeries.C w)

def constHom (π : W) : W →+* UVCrossingModel W π :=
  (mk π).comp (MvPowerSeries.C : W →+* MvPowerSeries (Fin 2) W)

theorem constHom_apply (π : W) (w : W) : constHom π w = const π w := rfl

theorem mk_surjective (π : W) : Function.Surjective (mk (W := W) π) :=
  Ideal.Quotient.mk_surjective

end UVCrossingModel

abbrev wittCrossingModel (p : ℕ) [Fact p.Prime] (k : Type u) [Field k] : Type u :=
  UVCrossingModel (WittVector p k) (p : WittVector p k)

section VariableSwap

variable {W : Type u} [CommRing W]

def uvSwapEquiv : MvPowerSeries (Fin 2) W ≃+* MvPowerSeries (Fin 2) W :=
  (MvPowerSeries.renameEquiv W (Equiv.swap (0 : Fin 2) 1)).toRingEquiv

theorem uvSwapEquiv_apply (f : MvPowerSeries (Fin 2) W) :
    uvSwapEquiv f = MvPowerSeries.rename (⇑(Equiv.swap (0 : Fin 2) 1)) f := rfl

theorem uvSwapEquiv_X_zero :
    uvSwapEquiv (MvPowerSeries.X (0 : Fin 2) : MvPowerSeries (Fin 2) W) =
      MvPowerSeries.X 1 := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_X, Equiv.swap_apply_left]

theorem uvSwapEquiv_X_one :
    uvSwapEquiv (MvPowerSeries.X (1 : Fin 2) : MvPowerSeries (Fin 2) W) =
      MvPowerSeries.X 0 := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_X, Equiv.swap_apply_right]

theorem uvSwapEquiv_C (w : W) :
    uvSwapEquiv (MvPowerSeries.C w : MvPowerSeries (Fin 2) W) = MvPowerSeries.C w := by
  rw [uvSwapEquiv_apply, MvPowerSeries.rename_C]

theorem uvSwapEquiv_crossing (π : W) :
    uvSwapEquiv ((MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        MvPowerSeries.C π) =
      (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) * MvPowerSeries.X 1 -
        MvPowerSeries.C π := by
  rw [map_sub, map_mul, uvSwapEquiv_X_zero, uvSwapEquiv_X_one, uvSwapEquiv_C, mul_comm]

theorem map_uvSwapEquiv_uvCrossingIdeal (π : W) :
    Ideal.map (uvSwapEquiv (W := W)) (uvCrossingIdeal W π) = uvCrossingIdeal W π := by
  rw [show uvCrossingIdeal W π = Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) W) *
    MvPowerSeries.X 1 - MvPowerSeries.C π} from rfl, Ideal.map_span, Set.image_singleton,
    uvSwapEquiv_crossing]

end VariableSwap

namespace UVCrossingModel

variable {W : Type u} [CommRing W]

def crossingSwap (π : W) : UVCrossingModel W π ≃+* UVCrossingModel W π :=
  Ideal.quotientEquiv (uvCrossingIdeal W π) (uvCrossingIdeal W π) uvSwapEquiv
    (map_uvSwapEquiv_uvCrossingIdeal π).symm

theorem crossingSwap_mk (π : W) (f : MvPowerSeries (Fin 2) W) :
    crossingSwap π (UVCrossingModel.mk π f) = UVCrossingModel.mk π (uvSwapEquiv f) := rfl

def S (π : W) : UVCrossingModel W π := U π + V π

def D (π : W) : UVCrossingModel W π := U π - V π

theorem S_def (π : W) : S π = U π + V π := rfl

theorem D_def (π : W) : D π = U π - V π := rfl

def fixedSubring (π : W) : Subring (UVCrossingModel W π) :=
  RingHom.eqLocus
    (crossingSwap π : UVCrossingModel W π →+* UVCrossingModel W π) (RingHom.id _)

theorem mem_fixedSubring_iff {π : W} {x : UVCrossingModel W π} :
    x ∈ fixedSubring π ↔ crossingSwap π x = x :=
  Iff.rfl

end UVCrossingModel

end

end ModularCurve
