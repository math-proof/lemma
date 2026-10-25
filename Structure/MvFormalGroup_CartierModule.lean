import Mathlib
import Instance.MvFormalGroup_NegV2
import Instance.MvFormalGroup_CartierModule

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

namespace WittLaw

open MvPolynomial

variable (p : ℕ) [hp : Fact p.Prime]


variable (R : Type u) [CommRing R]

def addFam (n : ℕ) : MvPowerSeries (Fin 2 × ℕ) R :=
  ↑(MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p n))


variable {R}


end WittLaw

open MvPowerSeries WittLaw

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

structure CartierModule (p : ℕ) [Fact p.Prime] {d : ℕ} {R : Type u} [CommRing R]
    (Φ : MvFormalGroup d R) where

  toPowerSeries : Fin d → MvPowerSeries ℕ R

  constantCoeff_eq_zero : ∀ j, (toPowerSeries j).constantCoeff = 0

  subst_eq : ∀ j,
    subst (WittLaw.addFam p R) (toPowerSeries j) =
      subst
        (Sum.elim
          (fun l => subst (fun m => (X (0, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
          fun l => subst (fun m => (X (1, m) : MvPowerSeries (Fin 2 × ℕ) R)) (toPowerSeries l))
        (Φ.toPowerSeries j)

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


end CartierModule

namespace WittLaw

variable (p)

def pairFam (u : ℕ → MvPowerSeries ℕ R) : Fin 2 × ℕ → MvPowerSeries (Fin 2 × ℕ) R :=
  fun im => subst (blk im.1) (u im.2)

structure IsEndo (u : ℕ → MvPowerSeries ℕ R) : Prop where
  hasSubst : HasSubst u
  constantCoeff : ∀ n, (u n).constantCoeff = 0
  subst_addFam : ∀ n, subst (addFam p R) (u n) = subst (pairFam u) (addFam p R n)

variable {p}

omit hp in


variable (R)


variable {R}

omit hp in


variable (p R)


variable {p R}

omit hp in


end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


end CartierModule

namespace WittLaw


variable (p R) in


end WittLaw

namespace CartierModule

variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R} {Φ'' : MvFormalGroup d'' R}


namespace Examples


end Examples

end CartierModule

end MvFormalGroup

end
