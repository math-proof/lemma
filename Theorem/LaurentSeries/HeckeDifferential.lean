module

public import Mathlib
public import Theorem.LaurentSeries.HeckeOperator
public import Def.AlgebraicCurve_DifferentialPushPull
public import Def.AlgebraicCurve_RegularDifferentials
public import Instance.ModularCurve_HeckeDifferential
public import Abbrev.ModularCurve_HeckeDifferential

public noncomputable section

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve

namespace ModularCurve

section Euler

variable (R : Type*) [CommRing R]


@[simp] public theorem qEulerFun_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEulerFun R x).coeff n = (n : R) * x.coeff n := rfl


public theorem support_qEulerFun_subset (x : LaurentSeries R) :
    (qEulerFun R x).support ⊆ x.support := fun n hn => by
  contrapose! hn
  simp only [mem_support, ne_eq, not_not] at hn ⊢
  rw [qEulerFun_coeff, hn, mul_zero]


public theorem algebraMap_laurentSeries_apply_alt (c : R) :
    algebraMap R (LaurentSeries R) c = single 0 c := by
  have h1 : algebraMap R (PowerSeries R) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl


@[simp] public theorem qEuler_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEuler R x).coeff n = (n : R) * x.coeff n := rfl


public theorem qEuler_single (n : ℤ) (r : R) :
    qEuler R (single n r) = single n ((n : R) * r) := by
  ext m
  by_cases h : m = n
  · subst h; simp
  · simp [coeff_single_of_ne h]

end Euler

section Shortcuts

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

end Shortcuts

section QExpansion

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))


@[simp] public theorem qEulerOn_apply (x : F) : qEulerOn F x = qEuler L (x : LaurentSeries L) := rfl


@[simp] public theorem diffQExp_D (x : F) : diffQExp F (D L F x) = qEuler L (x : LaurentSeries L) :=
  (qEulerOn F).liftKaehlerDifferential_comp_D x


public theorem diffQExp_smul_D (f x : F) :
    diffQExp F (f • D L F x) = (f : LaurentSeries L) * qEuler L (x : LaurentSeries L) := by
  rw [map_smul, diffQExp_D]
  rfl

end QExpansion

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]


public theorem heckeDiffAlong_apply (ω : Ω[laurentBaseChange L (modularFunctionFieldFull N)⁄L]) :
    heckeDiffAlong L N ℓ ω =
      Differential.traceAlong (heckeBetaBar L N ℓ) (Differential.pullbackAlong (heckeAlphaBar L N ℓ) ω) :=
  rfl

end Hecke

section Bar

variable (N : ℕ)

variable [NeZero N]


public theorem heckeDiffBar_eq (ℓ : Nat.Primes) :
    heckeDiffBar N ℓ = (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
      Differential.correspondence (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)) :=
  rfl

