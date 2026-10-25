/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/FractionalIdeal/GroupAction.lean -/


import Abbrev.RingTheory.FractionalIdeal.GroupAction
import Lemma.Int.FractionalIdeal.GroupAction
/-!
# Tests for group actions on fractional ideals

Exercises the induced actions on fractional ideals over `ℤ`.
-/


noncomputable section

open scoped nonZeroDivisors Pointwise FractionalIdealUnits

namespace N150Test

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] :
    MulSemiringAction G (FractionalIdeal R⁰ K) :=
  inferInstance

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] :
    MulDistribMulAction G (FractionalIdeal R⁰ K)ˣ :=
  inferInstance

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] (g : G) (I : (FractionalIdeal R⁰ K)ˣ) :
    ((g • I : (FractionalIdeal R⁰ K)ˣ) : FractionalIdeal R⁰ K) =
      g • (I : FractionalIdeal R⁰ K) :=
  FractionalIdeal.units_smul_val g I

example {G R K : Type*} [Group G] [CommRing R] [IsDomain R]
    [CommRing K] [Algebra R K] [IsFractionRing R K]
    [MulSemiringAction G R] (g : G) (I J : (FractionalIdeal R⁰ K)ˣ) :
    g • (I * J) = g • I * g • J :=
  smul_mul' g I J

example (σ : RingAut ℤ) : RingAut (FractionalIdeal ℤ⁰ ℚ) :=
  FractionalIdeal.ringEquivOfRingEquivHom ℤ ℚ σ

example (I : FractionalIdeal ℤ⁰ ℚ) : (1 : RingAut ℤ) • I = I :=
  one_smul _ _

example (σ τ : RingAut ℤ) (I : FractionalIdeal ℤ⁰ ℚ) :
    (σ * τ) • I = σ • τ • I :=
  mul_smul _ _ _

example (σ : RingAut ℤ) : σ • (0 : FractionalIdeal ℤ⁰ ℚ) = 0 :=
  smul_zero _

example (σ : RingAut ℤ) : σ • (1 : FractionalIdeal ℤ⁰ ℚ) = 1 :=
  smul_one _

example (σ : RingAut ℤ) (I J : FractionalIdeal ℤ⁰ ℚ) :
    σ • (I + J) = σ • I + σ • J :=
  smul_add _ _ _

example (σ : RingAut ℤ) (I J : FractionalIdeal ℤ⁰ ℚ) :
    σ • (I * J) = σ • I * σ • J :=
  MulSemiringAction.smul_mul σ I J

example (σ : RingAut ℤ) (I : FractionalIdeal ℤ⁰ ℚ) :
    σ • I = FractionalIdeal.ringEquivOfRingEquiv ℚ ℚ σ I :=
  FractionalIdeal.smul_def σ I

example (σ : RingAut ℤ) (I : FractionalIdeal ℤ⁰ ℚ) (x : ℚ) :
    x ∈ σ • I ↔ ∃ y ∈ I,
      IsFractionRing.ringEquivOfRingEquiv (K := ℚ) (L := ℚ) σ y = x :=
  FractionalIdeal.mem_smul_iff_exists σ I x

example (σ : RingAut ℤ) (I : FractionalIdeal ℤ⁰ ℚ) (x : ℚ) :
    x ∈ σ • I ↔
      (IsFractionRing.ringEquivOfRingEquiv (K := ℚ) (L := ℚ) σ).symm x ∈ I :=
  FractionalIdeal.mem_smul_iff σ I x

example (σ : RingAut ℤ) (I : Ideal ℤ) :
    σ • (I : FractionalIdeal ℤ⁰ ℚ) =
      ((σ • I : Ideal ℤ) : FractionalIdeal ℤ⁰ ℚ) :=
  FractionalIdeal.smul_coeIdeal σ I

end N150Test
end
