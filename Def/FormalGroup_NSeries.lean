import Mathlib

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 200000
set_option maxHeartbeats 1600000

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

noncomputable def eval (F : FormalGroup R) (x y : A) : A :=
  letI : UniformSpace R := ⊥
  MvPowerSeries.eval₂ (algebraMap R A) ![x, y] F.toPowerSeries

end FormalGroup

end

end

end

section
section

open MvPowerSeries IsLocalRing

noncomputable section

namespace FormalGroup

variable {R : Type*} [CommRing R]
variable {A : Type*} [CommRing A] [UniformSpace A] [Algebra R A]

noncomputable def nthSeries (F : FormalGroup R) : ℕ → PowerSeries R
  | 0 => 0
  | n + 1 => MvPowerSeries.subst ![F.nthSeries n, PowerSeries.X] F.toPowerSeries


noncomputable def evalSeries (f : PowerSeries R) (x : A) : A :=
  letI : UniformSpace R := ⊥
  PowerSeries.eval₂ (algebraMap R A) x f


noncomputable def evalNSMul (F : FormalGroup R) : ℕ → A → A
  | 0, _ => 0
  | n + 1, x => F.eval (F.evalNSMul n x) x

end FormalGroup

end

end

end

section
section

open scoped Classical

namespace MvPowerSeries
variable {σ : Type*} {R : Type*} [CommRing R]

noncomputable def pderivLin (i : σ) : MvPowerSeries σ R →ₗ[R] MvPowerSeries σ R where
  toFun F := (fun d => (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F :
              MvPowerSeries σ R)
  map_add' F G := by
    funext d
    show (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) (F + G)
       = (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F
       + (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) G
    rw [map_add, smul_add]
  map_smul' r F := by
    funext d
    show (d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) (r • F)
       = r • ((d i + 1 : ℕ) • MvPowerSeries.coeff (d + Finsupp.single i 1) F)
    rw [map_smul, smul_comm]

end MvPowerSeries

end

end

section
section

noncomputable section

open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def partialX : MvPowerSeries (Fin 2) R :=
  MvPowerSeries.pderivLin (0 : Fin 2) F.toPowerSeries


noncomputable def invDiffDenom : PowerSeries R :=
  MvPowerSeries.subst ![(0 : PowerSeries R), PowerSeries.X] F.partialX


noncomputable def invDiff : PowerSeries R :=
  PowerSeries.invOfUnit F.invDiffDenom (1 : Rˣ)

end FormalGroup

end

end

end

section
section

set_option maxHeartbeats 1200000

noncomputable section
open PowerSeries MvPowerSeries

namespace FormalGroup

variable {R : Type*} [CommRing R] (F : FormalGroup R)

noncomputable def qFoldSeriesB (q : ℕ) : PowerSeries R :=
  PowerSeries.mk fun k => if q ∣ k ∧ q ≤ k then PowerSeries.coeff k (F.nthSeries q) else 0

end FormalGroup

end

end

end
