module

public import Mathlib
public import Def.FormalGroup_NegV2
public import Def.FormalGroup_CartierModule
public import Def.PowerSeries_CartierModuleHomothety
public import Abbrev.MvFormalGroup_CartierModuleWittAction

@[expose] public section

set_option autoImplicit false

noncomputable section

universe u


namespace MvFormalGroup

open MvPowerSeries WittLaw

namespace WittLaw

variable (p : ℕ) [hp : Fact p.Prime] {R : Type u} [CommRing R]

def mulPoly (w : WittVector p R) (n : ℕ) : MvPolynomial ℕ R :=
  (cVec p w * WittVector.mk p (MvPolynomial.X : ℕ → MvPolynomial ℕ R)).coeff n

def mulFam (w : WittVector p R) : ℕ → MvPowerSeries ℕ R := fun n => (mulPoly p w n : MvPowerSeries ℕ R)

variable {p}

def verPoly (R : Type u) [CommRing R] : ℕ → MvPolynomial ℕ R
  | 0 => 0
  | n + 1 => MvPolynomial.X n

omit hp in
def xVec (R : Type u) [CommRing R] (i : Fin 2) : WittVector p (MvPolynomial (Fin 2 × ℕ) R) :=
  WittVector.mk p fun m => MvPolynomial.X (i, m)

def addPolyR (R : Type u) [CommRing R] (m : ℕ) : MvPolynomial (Fin 2 × ℕ) R :=
  MvPolynomial.map (Int.castRingHom R) (WittVector.wittAdd p m)

end WittLaw

namespace CartierModule

variable {p : ℕ} [hp : Fact p.Prime] {d d' : ℕ} {R : Type u} [CommRing R]
variable {Φ : MvFormalGroup d R} {Φ' : MvFormalGroup d' R}

def wittSMul [Φ.IsComm] (w : WittVector p R) : CartierModule p Φ →+ CartierModule p Φ :=
  precomp (WittLaw.isEndo_mulFam w)

def mapLinear [Φ.IsComm] [Φ'.IsComm] (φ : Φ.Hom Φ') :
    CartierModule p Φ →ₗ[WittVector p R] CartierModule p Φ' :=
  { map φ with map_smul' := fun w f => map_smul_witt φ w f }


end CartierModule

end MvFormalGroup

end
