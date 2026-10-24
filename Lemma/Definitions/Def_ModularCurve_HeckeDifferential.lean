import Mathlib
import Lemma.Definitions.Def_ModularCurve_HeckeOperator
import Lemma.Definitions.Def_AlgebraicCurve_DifferentialPushPull
import Lemma.Definitions.Def_AlgebraicCurve_RegularDifferentials

set_option autoImplicit false

noncomputable section

open HahnSeries KaehlerDifferential AlgebraicCurve

namespace ModularCurve

section Euler

variable (R : Type*) [CommRing R]

def qEulerFun (x : LaurentSeries R) : LaurentSeries R where
  coeff n := (n : R) * x.coeff n
  isPWO_support' := x.isPWO_support.mono fun n hn => by
    simp only [Function.mem_support, ne_eq] at hn ⊢
    intro h
    exact hn (by rw [h, mul_zero])

@[simp] theorem qEulerFun_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEulerFun R x).coeff n = (n : R) * x.coeff n := rfl

theorem support_qEulerFun_subset (x : LaurentSeries R) :
    (qEulerFun R x).support ⊆ x.support := fun n hn => by
  contrapose! hn
  simp only [mem_support, ne_eq, not_not] at hn ⊢
  rw [qEulerFun_coeff, hn, mul_zero]

theorem algebraMap_laurentSeries_apply_alt (c : R) :
    algebraMap R (LaurentSeries R) c = single 0 c := by
  have h1 : algebraMap R (PowerSeries R) c = PowerSeries.C c := by simp
  rw [HahnSeries.algebraMap_apply', h1, HahnSeries.ofPowerSeries_C]
  rfl

def qEuler : Derivation R (LaurentSeries R) (LaurentSeries R) where
  toFun := qEulerFun R
  map_add' x y := by
    ext n
    simp only [qEulerFun_coeff, coeff_add, mul_add]
  map_smul' r x := by
    ext n
    simp only [RingHom.id_apply, qEulerFun_coeff]
    rw [Algebra.smul_def, algebraMap_laurentSeries_apply_alt, coeff_single_zero_mul, HahnSeries.coeff_smul,
      qEulerFun_coeff, smul_eq_mul]
    ring
  map_one_eq_zero' := by
    ext n
    simp only [LinearMap.coe_mk, AddHom.coe_mk, qEulerFun_coeff, coeff_zero]
    by_cases hn : n = 0
    · subst hn; simp
    · rw [coeff_one, if_neg hn, mul_zero]
  leibniz' x y := by
    ext a
    simp only [LinearMap.coe_mk, AddHom.coe_mk, qEulerFun_coeff, coeff_add', Pi.add_apply,
      smul_eq_mul]
    rw [coeff_mul,
      coeff_mul_right' (x := x) (y := qEulerFun R y) y.isPWO_support (support_qEulerFun_subset R y),
      coeff_mul_right' (x := y) (y := qEulerFun R x) x.isPWO_support (support_qEulerFun_subset R x),
      Finset.mul_sum]
    have hswap : ∑ ij ∈ Finset.antidiagonal y.isPWO_support x.isPWO_support a,
        y.coeff ij.1 * (qEulerFun R x).coeff ij.2
        = ∑ ij ∈ Finset.antidiagonal x.isPWO_support y.isPWO_support a,
            (ij.1 : R) * x.coeff ij.1 * y.coeff ij.2 := by
      refine Finset.sum_nbij' Prod.swap Prod.swap ?_ ?_ ?_ ?_ ?_
      · intro ij hij
        exact Finset.swap_mem_antidiagonal.mpr hij
      · intro ij hij
        exact Finset.swap_mem_antidiagonal.mpr hij
      · intro ij _; rfl
      · intro ij _; rfl
      · intro ij _
        simp only [Prod.fst_swap, Prod.snd_swap, qEulerFun_coeff]
        ring
    rw [hswap, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun ij hij => ?_
    rw [Finset.mem_antidiagonal] at hij
    rw [qEulerFun_coeff, ← hij.2.2, Int.cast_add]
    ring

@[simp] theorem qEuler_coeff (x : LaurentSeries R) (n : ℤ) :
    (qEuler R x).coeff n = (n : R) * x.coeff n := rfl

theorem qEuler_single (n : ℤ) (r : R) :
    qEuler R (single n r) = single n ((n : R) * r) := by
  ext m
  by_cases h : m = n
  · subst h; simp
  · simp [coeff_single_of_ne h]

end Euler

section Shortcuts

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

set_option synthInstance.maxHeartbeats 400000 in
instance instAlgebraIntermediateFieldLaurent : Algebra L F := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instModuleKaehlerIntermediateFieldLaurent : Module L Ω[F⁄L] := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
instance instIsScalarTowerKaehlerIntermediateFieldLaurent : IsScalarTower L F Ω[F⁄L] :=
  inferInstance

instance instIsScalarTowerIntermediateFieldLaurent : IsScalarTower L F (LaurentSeries L) :=
  ⟨fun c f x => by
    show ((c • f : F) : LaurentSeries L) * x = c • ((f : LaurentSeries L) * x)
    rw [IntermediateField.coe_smul, Algebra.smul_def, algebraMap_laurentSeries_eq_single,
      ← C_apply, mul_assoc, C_mul_eq_smul]⟩

end Shortcuts

section QExpansion

variable {L : Type*} [Field L] (F : IntermediateField L (LaurentSeries L))

def qEulerOn : Derivation L F (LaurentSeries L) :=
  (qEuler L).compAlgebraMap F

@[simp] theorem qEulerOn_apply (x : F) : qEulerOn F x = qEuler L (x : LaurentSeries L) := rfl

def diffQExp : Ω[F⁄L] →ₗ[F] LaurentSeries L :=
  (qEulerOn F).liftKaehlerDifferential

@[simp] theorem diffQExp_D (x : F) : diffQExp F (D L F x) = qEuler L (x : LaurentSeries L) :=
  (qEulerOn F).liftKaehlerDifferential_comp_D x

theorem diffQExp_smul_D (f x : F) :
    diffQExp F (f • D L F x) = (f : LaurentSeries L) * qEuler L (x : LaurentSeries L) := by
  rw [map_smul, diffQExp_D]
  rfl

end QExpansion

section Hecke

variable (L : Type*) [Field L] [Algebra ℚ L] (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

def heckeDiffAlong :
    Ω[laurentBaseChange L (modularFunctionFieldFull N)⁄L] →ₗ[L]
      Ω[laurentBaseChange L (modularFunctionFieldFull N)⁄L] :=
  Differential.correspondence (heckeBetaBar L N ℓ) (heckeAlphaBar L N ℓ)

theorem heckeDiffAlong_apply (ω : Ω[laurentBaseChange L (modularFunctionFieldFull N)⁄L]) :
    heckeDiffAlong L N ℓ ω =
      Differential.traceAlong (heckeBetaBar L N ℓ) (Differential.pullbackAlong (heckeAlphaBar L N ℓ) ω) :=
  rfl

end Hecke

section Bar

variable (N : ℕ)

variable [NeZero N]

def heckeDiffBar (ℓ : Nat.Primes) :
    Module.End (AlgebraicClosure ℚ) Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩
  heckeDiffAlong (AlgebraicClosure ℚ) N ℓ

theorem heckeDiffBar_eq (ℓ : Nat.Primes) :
    heckeDiffBar N ℓ = (haveI : NeZero (ℓ : ℕ) := ⟨ℓ.2.ne_zero⟩;
      Differential.correspondence (heckeBetaBar (AlgebraicClosure ℚ) N ℓ)
        (heckeAlphaBar (AlgebraicClosure ℚ) N ℓ)) :=
  rfl

abbrev diffQExpBar : Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] →ₗ[modularFunctionFieldBar N]
    LaurentSeries (AlgebraicClosure ℚ) :=
  diffQExp (modularFunctionFieldBar N)

abbrev regularDifferentialsBar : Submodule (AlgebraicClosure ℚ)
    Ω[modularFunctionFieldBar N⁄AlgebraicClosure ℚ] :=
  regularDifferentials (AlgebraicClosure ℚ) (modularFunctionFieldBar N)

end Bar

end ModularCurve

end
