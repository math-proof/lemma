import Mathlib
import Class.AlgebraicCurve_DivisorPushPull
import Structure.AlgebraicCurve_AdelicIndex

set_option autoImplicit false

noncomputable section

namespace AlgebraicCurve

structure PoleDivisorPackage (K F : Type*) [Field K] [Field F] [Algebra K F] where

  x : F

  B : Divisor K F

  hB_eff : 0 ≤ B

  hx_mem : x ∈ LSpace B

  n : ℕ

  hn_pos : 0 < n

  degB_eq : Divisor.degree B = n

  c : ℕ

  u : Fin n → F

  hu_mem : ∀ i, u i ∈ LSpace (c • B)

  lin_indep : LinearIndependent K (fun p : ℕ × Fin n => x ^ p.1 * u p.2)


variable {K E F : Type*} [Field K] [Field E] [Field F]
  [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F]

structure TranscendenceTower (K E F : Type*) [Field K] [Field E] [Field F]
    [Algebra K E] [Algebra K F] [Algebra E F] [IsScalarTower K E F] where

  x : E

  hx_indep : LinearIndependent K (fun j : ℕ => x ^ j)

  v : Place K E

  hvdeg : v.deg = 1

  hxv : v.ord x = -1

  hxreg : ∀ u : Place K E, u ≠ v → 0 ≤ u.ord x

namespace TranscendenceTower

variable (T : TranscendenceTower K E F)


def poleDivisor [Algebra.IsSeparable E F] [HasPrincipalDivisors K F] : Divisor K F :=
  Divisor.pullback F (Finsupp.single T.v 1)


end TranscendenceTower

structure IntegralBasisInLSpace [Algebra.IsSeparable E F] [HasPrincipalDivisors K F]
    (T : TranscendenceTower K E F) where

  c : ℕ

  u : Fin (Module.finrank E F) → F

  hu_indep : LinearIndependent E u

  hu_mem : ∀ i, u i ∈ LSpace (c • T.poleDivisor)

variable (K E F) in


variable (K E F) in


variable (K E F) in


end AlgebraicCurve

end
