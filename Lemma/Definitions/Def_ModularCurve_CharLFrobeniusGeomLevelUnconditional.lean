import Mathlib
import Lemma.Definitions.Def_ModularCurve_JqCoeff
import Lemma.Definitions.Def_AlgebraicCurve_RatFuncPlaces
import Lemma.Definitions.Def_AlgebraicCurve_DivisorPushPull
import Theorems.Thm_ModularCurve_qExpand_jqModC_eq_pow_unconditional
import Lemma.Definitions.Def_ModularCurve_CharLFrobeniusGeomLevel

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

open AlgebraicCurve

namespace ModularCurve

section qExpandAlgC


end qExpandAlgC

section FrobeniusGeomLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

theorem charP_laurentSeries_alt : CharP (LaurentSeries K) ℓ :=
  charP_of_injective_algebraMap (algebraMap K (LaurentSeries K)).injective ℓ

theorem qExpand_jqNModC_eq_pow_unconditional_def :
    qExpand K ℓ (jqNModC K N) = (jqNModC K N) ^ ℓ := by
  rw [jqNModC, qExpand_qExpand, qExpand_congr (mul_comm ℓ N), ← qExpand_qExpand,
    qExpand_jqModC_eq_pow_unconditional K, map_pow]

theorem frobeniusGeomLevel_map_le_unconditional :
    (modularFunctionFieldC K N).map (qExpandAlgC K ℓ) ≤ modularFunctionFieldC K N := by
  show (IntermediateField.adjoin K {jqModC K, jqNModC K N}).map (qExpandAlgC K ℓ) ≤ _
  rw [IntermediateField.adjoin_map, Set.image_pair, IntermediateField.adjoin_le_iff]
  rintro x (rfl | rfl)
  · show qExpandAlgC K ℓ (jqModC K) ∈ modularFunctionFieldC K N
    rw [qExpandAlgC_apply, qExpand_jqModC_eq_pow_unconditional K]
    exact pow_mem (jqModC_mem K N) ℓ
  · show qExpandAlgC K ℓ (jqNModC K N) ∈ modularFunctionFieldC K N
    rw [qExpandAlgC_apply, qExpand_jqNModC_eq_pow_unconditional_def K N]
    exact pow_mem (jqNModC_mem K N) ℓ

def frobeniusGeomLevelUnconditional :
    modularFunctionFieldC K N →ₐ[K] modularFunctionFieldC K N :=
  (IntermediateField.inclusion (frobeniusGeomLevel_map_le_unconditional K N)).comp
    (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).toAlgHom

@[simp]
theorem frobeniusGeomLevelUnconditional_apply_coe (x : modularFunctionFieldC K N) :
    (frobeniusGeomLevelUnconditional K N (ℓ := ℓ) x : LaurentSeries K)
      = qExpand K ℓ (x : LaurentSeries K) := by
  refine (IntermediateField.coe_inclusion (frobeniusGeomLevel_map_le_unconditional K N)
    _).trans ?_
  exact coe_frobeniusGeomLevelEquiv_apply K N x

theorem frobeniusGeomLevelUnconditional_injective :
    Function.Injective (frobeniusGeomLevelUnconditional K N (ℓ := ℓ)) := by
  intro x y h
  have h' := congrArg (fun z : modularFunctionFieldC K N => (z : LaurentSeries K)) h
  simp only [frobeniusGeomLevelUnconditional_apply_coe] at h'
  exact Subtype.ext (qExpand_injective _ h')

theorem exists_frobeniusGeomLevelUnconditional_eq_iff (x : modularFunctionFieldC K N) :
    (∃ y, frobeniusGeomLevelUnconditional K N (ℓ := ℓ) y = x)
      ↔ (x : LaurentSeries K) ∈ frobeniusGeomLevelImage K N (ℓ := ℓ) := by
  constructor
  · rintro ⟨y, rfl⟩
    rw [frobeniusGeomLevelUnconditional_apply_coe]
    exact ⟨(y : LaurentSeries K), y.2, rfl⟩
  · rintro ⟨y, hy, hyx⟩
    refine ⟨⟨y, hy⟩, Subtype.ext ?_⟩
    rw [frobeniusGeomLevelUnconditional_apply_coe]
    exact hyx

theorem pow_mem_frobeniusGeomLevelImage_unconditional
    {x : LaurentSeries K} (hx : x ∈ modularFunctionFieldC K N) :
    x ^ ℓ ∈ frobeniusGeomLevelImage K N (ℓ := ℓ) := by
  haveI : CharP (LaurentSeries K) ℓ := charP_laurentSeries_alt K
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · rw [← qExpand_jqModC_eq_pow_unconditional K]
      exact ⟨jqModC K, jqModC_mem K N, rfl⟩
    · rw [← qExpand_jqNModC_eq_pow_unconditional_def K N]
      exact ⟨jqNModC K N, jqNModC_mem K N, rfl⟩
  | algebraMap c =>
    rw [← map_pow]
    exact (frobeniusGeomLevelImage K N (ℓ := ℓ)).algebraMap_mem (c ^ ℓ)
  | add y z _ _ hy hz =>
    rw [add_pow_char]
    exact add_mem hy hz
  | inv y _ hy =>
    rw [inv_pow]
    exact inv_mem hy
  | mul y z _ _ hy hz =>
    rw [mul_pow]
    exact mul_mem hy hz

theorem exists_frobeniusGeomLevelUnconditional_eq_pow (x : modularFunctionFieldC K N) :
    ∃ y, frobeniusGeomLevelUnconditional K N (ℓ := ℓ) y = x ^ ℓ := by
  rw [exists_frobeniusGeomLevelUnconditional_eq_iff]
  show (x : LaurentSeries K) ^ ℓ ∈ frobeniusGeomLevelImage K N (ℓ := ℓ)
  exact pow_mem_frobeniusGeomLevelImage_unconditional K N x.2

end FrobeniusGeomLevel

section ValSubringRoots


end ValSubringRoots

section PlaceLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

@[reducible] def frobImageAlgebraUnconditional :
    Algebra (frobeniusGeomLevelImage K N (ℓ := ℓ)) (modularFunctionFieldC K N) :=
  (IntermediateField.inclusion
    (frobeniusGeomLevel_map_le_unconditional K N)).toRingHom.toAlgebra

theorem frobImageTowerUnconditional :
    letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
    IsScalarTower K (frobeniusGeomLevelImage K N (ℓ := ℓ)) (modularFunctionFieldC K N) :=
  letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
  IsScalarTower.of_algebraMap_eq fun _ => Subtype.ext rfl

theorem frobImageIsIntegralUnconditional :
    letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
    Algebra.IsIntegral (frobeniusGeomLevelImage K N (ℓ := ℓ))
      (modularFunctionFieldC K N) := by
  letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
  refine ⟨fun x => ?_⟩
  refine ⟨Polynomial.X ^ ℓ - Polynomial.C
    ⟨(x : LaurentSeries K) ^ ℓ, pow_mem_frobeniusGeomLevelImage_unconditional K N x.2⟩,
    Polynomial.monic_X_pow_sub_C _ (Fact.out : ℓ.Prime).pos.ne', ?_⟩
  rw [Polynomial.eval₂_sub, Polynomial.eval₂_X_pow, Polynomial.eval₂_C, sub_eq_zero]
  exact Subtype.ext rfl

def frobOnPlacesGeomLevelUnconditional (w : Place K (modularFunctionFieldC K N)) :
    Place K (modularFunctionFieldC K N) :=
  letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
  letI := frobImageTowerUnconditional K N (ℓ := ℓ)
  letI := frobImageIsIntegralUnconditional K N (ℓ := ℓ)
  (Place.congrEquiv (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).toRingEquiv
    (fun a => (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).commutes a)).symm
    (w.restrict (frobeniusGeomLevelImage K N (ℓ := ℓ)))

theorem mem_frobOnPlacesGeomLevelUnconditional_iff
    (w : Place K (modularFunctionFieldC K N)) (x : modularFunctionFieldC K N) :
    x ∈ (frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w).toValuationSubring
      ↔ frobeniusGeomLevelUnconditional K N (ℓ := ℓ) x ∈ w.toValuationSubring := by
  letI := frobImageAlgebraUnconditional K N (ℓ := ℓ)
  letI := frobImageTowerUnconditional K N (ℓ := ℓ)
  letI := frobImageIsIntegralUnconditional K N (ℓ := ℓ)
  rw [show frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w
      = (Place.congrEquiv (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).toRingEquiv
          (fun a => (frobeniusGeomLevelEquiv K N (ℓ := ℓ)).commutes a)).symm
          (w.restrict (frobeniusGeomLevelImage K N (ℓ := ℓ))) from rfl,
    Place.congrEquiv_symm_apply, Place.congrRingEquiv_toValuationSubring,
    ValuationSubring.mem_comap, RingEquiv.symm_symm]
  exact Iff.rfl

theorem frobOnPlacesGeomLevelUnconditional_injective :
    Function.Injective (frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ)) := by
  intro w w' h
  ext1
  refine SetLike.ext fun x => ?_
  obtain ⟨y, hy⟩ := exists_frobeniusGeomLevelUnconditional_eq_pow K N x
  rw [mem_valuationSubring_iff_pow_mem (ℓ := ℓ) w.toValuationSubring x, ← hy,
    ← mem_frobOnPlacesGeomLevelUnconditional_iff K N w y, h,
    mem_frobOnPlacesGeomLevelUnconditional_iff K N w' y, hy,
    ← mem_valuationSubring_iff_pow_mem (ℓ := ℓ) w'.toValuationSubring x]

open Classical in

def verOnPlacesGeomLevelUnconditional (u : Place K (modularFunctionFieldC K N)) :
    Place K (modularFunctionFieldC K N) :=
  if h : ∃ w, frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w = u then h.choose else u

theorem verOnPlacesGeomLevelUnconditional_frobOnPlacesGeomLevelUnconditional
    (w : Place K (modularFunctionFieldC K N)) :
    verOnPlacesGeomLevelUnconditional K N (ℓ := ℓ)
      (frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w) = w := by
  rw [verOnPlacesGeomLevelUnconditional, dif_pos ⟨w, rfl⟩]
  exact frobOnPlacesGeomLevelUnconditional_injective K N
    (Exists.choose_spec
      (⟨w, rfl⟩ : ∃ w', frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w'
        = frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w))

end PlaceLevel

section DivisorLevel

variable (K : Type*) [Field K] (N : ℕ) [NeZero N]
variable {ℓ : ℕ} [Fact ℓ.Prime] [CharP K ℓ]

def frobeniusPushforwardGeomLevelUnconditional :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  Finsupp.mapDomain.addMonoidHom (frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ))

def frobeniusPullbackGeomLevelUnconditional :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  Finsupp.liftAddHom fun v =>
    (Finsupp.singleAddHom (verOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) v)).comp
      (AddMonoidHom.mulRight (ℓ : ℤ))

def heckeFibreGeomLevelUnconditional :
    Divisor K (modularFunctionFieldC K N) →+ Divisor K (modularFunctionFieldC K N) :=
  frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ)
    + frobeniusPullbackGeomLevelUnconditional K N (ℓ := ℓ)

@[simp]
theorem frobeniusPushforwardGeomLevelUnconditional_single
    (w : Place K (modularFunctionFieldC K N)) (n : ℤ) :
    frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ) (Finsupp.single w n)
      = Finsupp.single (frobOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w) n := by
  simp [frobeniusPushforwardGeomLevelUnconditional, Finsupp.mapDomain.addMonoidHom_apply,
    Finsupp.mapDomain_single]

@[simp]
theorem frobeniusPullbackGeomLevelUnconditional_single
    (w : Place K (modularFunctionFieldC K N)) (n : ℤ) :
    frobeniusPullbackGeomLevelUnconditional K N (ℓ := ℓ) (Finsupp.single w n)
      = Finsupp.single (verOnPlacesGeomLevelUnconditional K N (ℓ := ℓ) w) (n * ℓ) := by
  simp [frobeniusPullbackGeomLevelUnconditional]

theorem frobeniusPullbackGeomLevelUnconditional_pushforward
    (D : Divisor K (modularFunctionFieldC K N)) :
    frobeniusPullbackGeomLevelUnconditional K N (ℓ := ℓ)
        (frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ) D) = (ℓ : ℤ) • D := by
  induction D using Finsupp.induction with
  | zero => simp
  | single_add v n D _ _ ih =>
    rw [map_add, map_add, ih, frobeniusPushforwardGeomLevelUnconditional_single,
      frobeniusPullbackGeomLevelUnconditional_single,
      verOnPlacesGeomLevelUnconditional_frobOnPlacesGeomLevelUnconditional,
      smul_add, Finsupp.smul_single, smul_eq_mul, mul_comm]

theorem eichlerShimura_special_fibre_geom_level_unconditional
    (D : Divisor K (modularFunctionFieldC K N)) :
    frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ)
        (frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ) D)
      - heckeFibreGeomLevelUnconditional K N (ℓ := ℓ)
          (frobeniusPushforwardGeomLevelUnconditional K N (ℓ := ℓ) D)
      + (ℓ : ℤ) • D = 0 := by
  rw [heckeFibreGeomLevelUnconditional, AddMonoidHom.add_apply,
    frobeniusPullbackGeomLevelUnconditional_pushforward]
  abel

end DivisorLevel

end ModularCurve
