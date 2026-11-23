module

public import Mathlib
public import Structure.MvFormalGroup_CartierModule

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u

namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' d'' : ℕ} {R : Type u} [CommRing R]

def inBlk (i : Fin 2) (a : Fin d → MvPowerSeries ℕ R) : Fin d → MvPowerSeries (Fin 2 × ℕ) R :=
  fun l => subst (blk i) (a l)

end CartierModule

namespace WittLaw

def verFam (R : Type u) [CommRing R] : ℕ → MvPowerSeries ℕ R
  | 0 => 0
  | n + 1 => X n

def frobFam (p : ℕ) (R : Type u) [CommRing R] : ℕ → MvPowerSeries ℕ R :=
  fun n => X n ^ p

end WittLaw

end MvFormalGroup

end

end
