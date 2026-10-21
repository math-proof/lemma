import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

variable {R : Type*} [CommRing R]
private noncomputable def mulQuot (x y : R) : (R ⧸ Ideal.span {y}) →ₗ[R] (R ⧸ Ideal.span {x * y}) :=
  Submodule.mapQ (Ideal.span {y}) (Ideal.span {x * y}) (LinearMap.mulLeft R x) (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.mulLeft_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c, by ring⟩)
private lemma mulQuot_mk (x y r : R) : mulQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ (x * r) := rfl
private noncomputable def projQuot (x y : R) : (R ⧸ Ideal.span {x * y}) →ₗ[R] (R ⧸ Ideal.span {x}) :=
  Submodule.mapQ (Ideal.span {x * y}) (Ideal.span {x}) LinearMap.id (by
    intro z hz
    rw [Submodule.mem_comap, LinearMap.id_apply]
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hz
    exact Ideal.mem_span_singleton'.mpr ⟨c * y, by ring⟩)
private lemma projQuot_mk (x y r : R) : projQuot x y (Ideal.Quotient.mk _ r) = Ideal.Quotient.mk _ r := rfl
private lemma projQuot_surjective (x y : R) : Function.Surjective (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  exact ⟨Ideal.Quotient.mk _ r, rfl⟩
private lemma mulQuot_injective [IsDomain R] (x y : R) (hx : x ≠ 0) : Function.Injective (mulQuot x y) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro m hm
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [LinearMap.mem_ker, mulQuot_mk, Ideal.Quotient.eq_zero_iff_mem] at hm
  obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm
  rw [Ideal.Quotient.eq_zero_iff_mem]
  refine Ideal.mem_span_singleton'.mpr ⟨s, mul_left_cancel₀ hx ?_⟩
  rw [← hs]; ring
private lemma exact_mulQuot_projQuot (x y : R) : Function.Exact (mulQuot x y) (projQuot x y) := by
  intro m
  obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective m
  rw [projQuot_mk, Ideal.Quotient.eq_zero_iff_mem]
  constructor
  · intro hr
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp hr
    exact ⟨Ideal.Quotient.mk _ c, by rw [mulQuot_mk, mul_comm x c]⟩
  · rintro ⟨m', hm'⟩
    obtain ⟨r', rfl⟩ := Ideal.Quotient.mk_surjective m'
    rw [mulQuot_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem] at hm'
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hm'
    refine Ideal.mem_span_singleton'.mpr ⟨r' - s * y, ?_⟩
    have : r = x * r' - s * (x * y) := by rw [hs]; ring
    rw [this]; ring
private lemma length_quotient_mul [IsDomain R] (x y : R) (hx : x ≠ 0) :
    Module.length R (R ⧸ Ideal.span {x * y}) =
      Module.length R (R ⧸ Ideal.span {y}) + Module.length R (R ⧸ Ideal.span {x}) :=
  Module.length_eq_add_of_exact (mulQuot x y) (projQuot x y) (mulQuot_injective x y hx) (projQuot_surjective x y)
    (exact_mulQuot_projQuot x y)
private lemma length_quotient_pow [IsDomain R] (x : R) (hx : x ≠ 0) (m : ℕ) :
    Module.length R (R ⧸ Ideal.span {x ^ m}) = m * Module.length R (R ⧸ Ideal.span {x}) := by
  induction m with
  | zero =>
    rw [pow_zero, Nat.cast_zero, zero_mul, Module.length_eq_zero_iff, Ideal.span_singleton_one]
    infer_instance
  | succ m ih =>
    rw [pow_succ', length_quotient_mul x _ hx, ih, Nat.cast_succ]
    ring
private lemma length_quotient_unit_mul {a : R} (ha : IsUnit a) (x : R) :
    Module.length R (R ⧸ Ideal.span {a * x}) = Module.length R (R ⧸ Ideal.span {x}) := by
  rw [Ideal.span_singleton_mul_left_unit ha]
/--
[IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsDiscreteValuationRing_length_quotient_map_span_eq_length_mul_length.lean)
-/
@[path]
private lemma main
    {D L : Type*} [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] [CommRing L] [IsDomain L] [IsLocalRing L]
    (φ : D →+* L) (hφ0 : Function.Injective φ)
    (f : D) (hf : f ≠ 0) :
    Module.length L (L ⧸ Ideal.span {φ f}) =
      Module.length D (D ⧸ Ideal.span {f}) * Module.length L (L ⧸ Ideal.map φ (IsLocalRing.maximalIdeal D)) := by
  obtain ⟨t, ht⟩ := IsDiscreteValuationRing.exists_irreducible D
  have hmax : IsLocalRing.maximalIdeal D = Ideal.span {t} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer t).mp ht
  obtain ⟨m, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hf ht
  have ht0 : t ≠ 0 := ht.ne_zero
  have hφt0 : φ t ≠ 0 := fun h => ht0 (hφ0 (by rw [h, map_zero]))
  have hD : Module.length D (D ⧸ Ideal.span {(u : D) * t ^ m}) = m := by
    rw [length_quotient_unit_mul u.isUnit, length_quotient_pow t ht0, ← hmax]
    have h1 : Module.length D (D ⧸ IsLocalRing.maximalIdeal D) = 1 :=
      Module.length_eq_one_iff.mpr (isSimpleModule_iff_quot_maximal.mpr
        ⟨IsLocalRing.maximalIdeal D, inferInstance, ⟨LinearEquiv.refl D (D ⧸ IsLocalRing.maximalIdeal D)⟩⟩)
    rw [h1, mul_one]
  have hL : Module.length L (L ⧸ Ideal.span {φ ((u : D) * t ^ m)}) = m * Module.length L (L ⧸ Ideal.span {φ t}) := by
    rw [map_mul, map_pow, length_quotient_unit_mul (u.isUnit.map φ), length_quotient_pow (φ t) hφt0]
  rw [hL, hD, hmax, Ideal.map_span, Set.image_singleton]

-- created on 2026-10-20
