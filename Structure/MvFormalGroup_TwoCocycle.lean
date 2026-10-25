import Mathlib
import Class.MvFormalGroup_BasicV2
import Def.MvFormalGroup_TwoCocycle

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {n : ℕ} {R : Type*} [CommRing R]


structure IsSymmTwoCocycle (F : MvFormalGroup n R) (Γ : MvPowerSeries (Fin n ⊕ Fin n) R) : Prop where

  constantCoeff_eq_zero : Γ.constantCoeff = 0

  symm :
    subst
      (Sum.elim
        (fun j => (X (Sum.inr j) : MvPowerSeries (Fin n ⊕ Fin n) R))
        fun j => X (Sum.inl j))
      Γ = Γ

  cocycle :
    subst
        (Sum.elim
          (fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inl l)))
            (F.toPowerSeries j))
          fun j => X (Sum.inr (Sum.inr j)))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inl l) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inl l)))
        Γ
      =
    subst
        (Sum.elim
          (fun j => (X (Sum.inl j) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun j => subst
            (Sum.elim
              (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
              fun l => X (Sum.inr (Sum.inr l)))
            (F.toPowerSeries j))
        Γ
      + subst
        (Sum.elim
          (fun l => (X (Sum.inr (Sum.inl l)) : MvPowerSeries (Fin n ⊕ (Fin n ⊕ Fin n)) R))
          fun l => X (Sum.inr (Sum.inr l)))
        Γ


end MvFormalGroup

end
