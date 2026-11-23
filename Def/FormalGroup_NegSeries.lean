module

public import Def.FormalGroup_EndRingV2

@[expose] public section

set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace MvFormalGroup

variable {g h k : ℕ} {R : Type*} [CommRing R]


section NegSeries

variable {τ : Type*} (F : MvFormalGroup g R)

def negApprox (a : Fin g → MvPowerSeries τ R) : ℕ → Fin g → MvPowerSeries τ R
  | 0 => fun _ => 0
  | n + 1 => fun i =>
      negApprox a n i
        - homogeneousComponent (n + 1)
            (subst (Sum.elim a (negApprox a n)) (F.toPowerSeries i))

def negSeries (a : Fin g → MvPowerSeries τ R) : Fin g → MvPowerSeries τ R :=
  fun i => (fun d => coeff d (negApprox F a d.degree i) : (τ →₀ ℕ) → R)

end NegSeries


section InvSeries

variable (F : MvFormalGroup g R)

def invSeries : Fin g → MvPowerSeries (Fin g) R :=
  negSeries F fun j => X j

end InvSeries

end MvFormalGroup

end

end
