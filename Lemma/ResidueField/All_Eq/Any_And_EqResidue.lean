import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits CategoryTheory.MorphismProperty AlgebraicGeometry TopologicalSpace Opposite IsLocalRing
open scoped TensorProduct MonoidalCategory

universe u

set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

private lemma eq_one_of_pow_eq_one_of_residue_eq_one {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ}
    (hm : (m : ResidueField R) ≠ 0) {ζ : R} (hζ : ζ ^ m = 1) (h1 : residue R ζ = 1) : ζ = 1 := by
  have hgeom : (∑ i ∈ Finset.range m, ζ ^ i) * (ζ - 1) = 0 := by
    rw [geom_sum_mul, hζ, sub_self]
  have hunit : IsUnit (∑ i ∈ Finset.range m, ζ ^ i) := by
    rw [← residue_ne_zero_iff_isUnit, map_sum]
    simp only [map_pow, h1, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
    exact hm
  have := hunit.mul_left_cancel (hgeom.trans (mul_zero _).symm)
  exact sub_eq_zero.mp this
private lemma eq_of_pow_eq_one_of_residue_eq {R : Type*} [CommRing R] [IsLocalRing R] {m : ℕ}
    (hm : (m : ResidueField R) ≠ 0) {ζ₁ ζ₂ : R} (h₁ : ζ₁ ^ m = 1) (h₂ : ζ₂ ^ m = 1)
    (h : residue R ζ₁ = residue R ζ₂) : ζ₁ = ζ₂ := by
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  obtain ⟨u, rfl⟩ := IsUnit.of_pow_eq_one h₂ hm0
  have hu : u ^ m = 1 := Units.ext (by rw [Units.val_pow_eq_pow_val, Units.val_one]; exact h₂)
  have hz : (ζ₁ * ↑u⁻¹) ^ m = 1 := by
    rw [mul_pow, h₁, one_mul, ← Units.val_pow_eq_pow_val, inv_pow, hu, inv_one, Units.val_one]
  have hres : residue R (ζ₁ * ↑u⁻¹) = 1 := by
    rw [map_mul, h, ← map_mul, Units.mul_inv, map_one]
  have := eq_one_of_pow_eq_one_of_residue_eq_one hm hz hres
  calc ζ₁ = ζ₁ * ↑u⁻¹ * ↑u := by rw [Units.inv_mul_cancel_right]
    _ = ↑u := by rw [this, one_mul]
/--
[ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_residue_injOn_pow_eq_one_and_exists_residue_eq_of_isAlgClosed.lean)
-/
@[path]
private lemma main
    (K : Type*) [Field K] [IsAlgClosed K] (A : ValuationSubring K)
    (m : ℕ) (hm : (m : ResidueField ↥A) ≠ 0) :
    (∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂) ∧
    (∀ u : ResidueField ↥A, u ^ m = 1 → ∃ ζ : ↥A, ζ ^ m = 1 ∧ residue ↥A ζ = u) := by
  have hinj : ∀ ζ₁ ζ₂ : ↥A, ζ₁ ^ m = 1 → ζ₂ ^ m = 1 → residue ↥A ζ₁ = residue ↥A ζ₂ → ζ₁ = ζ₂ :=
    fun _ _ h₁ h₂ h => eq_of_pow_eq_one_of_residue_eq hm h₁ h₂ h
  refine ⟨hinj, fun u hu => ?_⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hm (by simp)
  let _ : NeZero m := ⟨hm0⟩
  have hmK : (m : K) ≠ 0 := by
    intro h0
    apply hm
    have hA : (m : ↥A) = 0 := by
      apply Subtype.ext
      simpa using h0
    rw [← map_natCast (residue ↥A), hA, map_zero]
  let _ : NeZero (m : K) := ⟨hmK⟩
  obtain ⟨ζ₀, hζ₀⟩ := HasEnoughRootsOfUnity.prim (M := K) (n := m)
  have hζ₀A : ζ₀ ∈ A := by
    rw [← A.valuation_le_one_iff]
    have hpow : A.valuation ζ₀ ^ m = 1 := by rw [← map_pow, hζ₀.pow_eq_one, map_one]
    exact ((pow_eq_one_iff.mp hpow).resolve_right hm0).le
  set ζA : ↥A := ⟨ζ₀, hζ₀A⟩ with hζA
  have hζAm : ζA ^ m = 1 := Subtype.ext (by simp [hζA, hζ₀.pow_eq_one])
  have hprim : IsPrimitiveRoot (residue ↥A ζA) m := by
    refine IsPrimitiveRoot.mk_of_lt _ (Nat.pos_of_ne_zero hm0) ?_ fun l hl0 hlm => ?_
    · rw [← map_pow, hζAm, map_one]
    · intro hl
      have hζl : ζA ^ l = 1 := by
        refine hinj _ _ ?_ (one_pow m) (by rwa [map_pow, map_one])
        rw [← pow_mul, mul_comm, pow_mul, hζAm, one_pow]
      have : ζ₀ ^ l = 1 := by
        have := congrArg Subtype.val hζl
        simpa [hζA] using this
      exact hζ₀.pow_ne_one_of_pos_of_lt hl0.ne' hlm this
  obtain ⟨k, -, hk⟩ := hprim.eq_pow_of_pow_eq_one hu
  refine ⟨ζA ^ k, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, hζAm, one_pow]
  · rw [map_pow, hk]

-- created on 2026-10-20
