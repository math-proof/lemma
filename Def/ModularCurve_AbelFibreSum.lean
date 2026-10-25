import Mathlib
import Lemma.ModularCurve.PeriodLattice

open UpperHalfPlane
open scoped MatrixGroups

namespace ModularCurve

noncomputable def valueMultiplicity (F : ℍ → ℂ) (t : ℂ) (τ : ℍ) : ℕ :=
  (meromorphicOrderAt (fun z : ℂ => F (ofComplex z) - t) (τ : ℂ)).untop₀.toNat

noncomputable def orbifoldIndex (N : ℕ) (τ : ℍ) : ℕ :=
  Nat.card (MulAction.stabilizer (CongruenceSubgroup.Gamma0 N) τ) / 2

noncomputable def abelFibreSum (N : ℕ) (F : ℍ → ℂ) (t : ℂ) :
    Module.Dual ℂ (CuspForm (CongruenceSubgroup.Gamma0 N) 2) :=
  ∑ᶠ ξ : Quotient (MulAction.orbitRel (CongruenceSubgroup.Gamma0 N) ℍ),
    ((valueMultiplicity F t ξ.out : ℂ) / (orbifoldIndex N ξ.out : ℂ)) •
      periodAlong N UpperHalfPlane.I ξ.out

end ModularCurve
