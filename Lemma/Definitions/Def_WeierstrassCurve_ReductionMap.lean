import Lemma.Definitions.Def_FLTPrelim_Ramification
import Lemma.Definitions.Def_FreyPackage_GaloisRep
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.RingTheory.Valuation.LocalSubring

set_option autoImplicit false

open IsLocalRing

namespace ValuationSubring

variable {L : Type*} [Field L]

lemma liesOverPrime_iff {A : ValuationSubring L} {q : ℕ} :
    A.LiesOverPrime q ↔ (q : L) ∈ A.nonunits :=
  Iff.rfl

lemma natCast_mem' (A : ValuationSubring L) (q : ℕ) : (q : L) ∈ A :=
  natCast_mem A.toSubring q

lemma natCast_mem_maximalIdeal_of_liesOverPrime {A : ValuationSubring L} {q : ℕ}
    (h : A.LiesOverPrime q) : (q : A) ∈ IsLocalRing.maximalIdeal A := by
  have : ((q : A) : L) ∈ A.nonunits := by
    simpa using liesOverPrime_iff.mp h
  exact A.coe_mem_nonunits_iff.mp this

theorem exists_liesOverPrime [CharZero L] {q : ℕ} (hq : q.Prime) :
    ∃ A : ValuationSubring L, A.LiesOverPrime q := by

  set R : Subring L := ⊥ with hR

  have hqR : ¬IsUnit ((q : ℕ) : R) := by
    rw [isUnit_iff_exists_inv]
    rintro ⟨y, hy⟩

    have hy' : (q : L) * (y : L) = 1 := by
      have := congrArg (R.subtype) hy
      simpa using this

    obtain ⟨n, hn⟩ := Subring.mem_bot.mp y.2
    rw [← hn] at hy'

    have hqn : (q : ℤ) * n = 1 := by
      have : (((q : ℤ) * n : ℤ) : L) = ((1 : ℤ) : L) := by push_cast; linear_combination hy'
      exact_mod_cast this

    have h1 : (q : ℤ) ≤ 1 := Int.le_of_dvd one_pos ⟨n, hqn.symm⟩
    have h2 : 2 ≤ q := hq.two_le
    omega

  obtain ⟨B, -, hB⟩ :=
    Ideal.image_subset_nonunits_valuationSubring (Ideal.span {((q : ℕ) : R)})
      (fun h => hqR (Ideal.span_singleton_eq_top.mp h))
  refine ⟨B, hB ⟨((q : ℕ) : R), Ideal.subset_span rfl, ?_⟩⟩
  simp

theorem charP_residueField_of_liesOverPrime_def {A : ValuationSubring L} {q : ℕ} (hq : q.Prime)
    (h : A.LiesOverPrime q) : CharP (IsLocalRing.ResidueField A) q := by
  rw [CharP.charP_iff_prime_eq_zero hq]

  have : ((q : ℕ) : IsLocalRing.ResidueField A) = IsLocalRing.residue A ((q : ℕ) : A) := by
    simp
  rw [this]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (natCast_mem_maximalIdeal_of_liesOverPrime h)

variable (K : Type*) [Field K] [Algebra K L]

lemma mem_inertiaSubgroupIn {A : ValuationSubring L} {σ : L ≃ₐ[K] L} :
    σ ∈ A.inertiaSubgroupIn K ↔
      ∃ h : σ ∈ A.decompositionSubgroup K, (⟨σ, h⟩ : A.decompositionSubgroup K) ∈
        A.inertiaSubgroup K := by
  constructor
  · rintro ⟨⟨τ, hτ⟩, hτI, rfl⟩
    exact ⟨hτ, hτI⟩
  · rintro ⟨h, hI⟩
    exact ⟨⟨σ, h⟩, hI, rfl⟩

end ValuationSubring

namespace ValuationSubring

variable {L : Type*} [Field L] {A : ValuationSubring L}

theorem mul_mem_nonunits {a x : L} (ha : a ∈ A) (hx : x ∈ A.nonunits) :
    a * x ∈ A.nonunits := by
  rw [mem_nonunits_iff] at hx ⊢
  calc A.valuation (a * x) = A.valuation a * A.valuation x := map_mul _ _ _
    _ ≤ 1 * A.valuation x := mul_le_mul_left ((A.valuation_le_one_iff a).mpr ha) _
    _ = A.valuation x := one_mul _
    _ < 1 := hx

theorem one_notMem_nonunits : (1 : L) ∉ A.nonunits := by
  simp [mem_nonunits_iff]

end ValuationSubring

namespace WeierstrassCurve

variable {L : Type*} [Field L] {A : ValuationSubring L}

private lemma some_congr {R : Type*} [CommRing R] {V : Affine R} {x₁ x₂ y₁ y₂ : R}
    (hx : x₁ = x₂) (hy : y₁ = y₂) (h₁ : V.Nonsingular x₁ y₁) (h₂ : V.Nonsingular x₂ y₂) :
    Affine.Point.some x₁ y₁ h₁ = Affine.Point.some x₂ y₂ h₂ := by
  subst hx; subst hy; rfl

variable (W : WeierstrassCurve A)

theorem Affine.Y_mem_of_X_mem {x y : L}
    (h : (W.map A.subtype).toAffine.Equation x y) (hx : x ∈ A) : y ∈ A := by
  by_contra hy

  have hy0 : y ≠ 0 := fun h0 => hy (h0 ▸ A.zero_mem)
  have hyinv : y⁻¹ ∈ A.nonunits := A.inv_mem_nonunits_iff.mpr (Or.inr hy)
  rw [equation_iff] at h

  have key : (1 : L) =
      (x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2 + (W.map A.subtype).toAffine.a₄ * x
          + (W.map A.subtype).toAffine.a₆) * (y⁻¹ * y⁻¹)
        - (W.map A.subtype).toAffine.a₁ * x * y⁻¹
        - (W.map A.subtype).toAffine.a₃ * y⁻¹ := by
    field_simp
    linear_combination h

  refine A.one_notMem_nonunits ?_
  rw [key]
  have ha₁ : (W.map A.subtype).toAffine.a₁ ∈ A := SetLike.coe_mem W.a₁
  have ha₂ : (W.map A.subtype).toAffine.a₂ ∈ A := SetLike.coe_mem W.a₂
  have ha₃ : (W.map A.subtype).toAffine.a₃ ∈ A := SetLike.coe_mem W.a₃
  have ha₄ : (W.map A.subtype).toAffine.a₄ ∈ A := SetLike.coe_mem W.a₄
  have ha₆ : (W.map A.subtype).toAffine.a₆ ∈ A := SetLike.coe_mem W.a₆
  have hcubic : x ^ 3 + (W.map A.subtype).toAffine.a₂ * x ^ 2
      + (W.map A.subtype).toAffine.a₄ * x + (W.map A.subtype).toAffine.a₆ ∈ A :=
    add_mem (add_mem (add_mem (pow_mem hx 3) (mul_mem ha₂ (pow_mem hx 2))) (mul_mem ha₄ hx)) ha₆
  exact sub_mem (sub_mem (A.mul_mem_nonunits hcubic (mul_mem hyinv hyinv))
      (A.mul_mem_nonunits (mul_mem ha₁ hx) hyinv))
    (A.mul_mem_nonunits ha₃ hyinv)

theorem map_residue_Δ_ne_zero_iff : (W.map (residue A)).Δ ≠ 0 ↔ IsUnit W.Δ := by
  rw [map_Δ]
  exact residue_ne_zero_iff_isUnit W.Δ

theorem Affine.equation_residue {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Equation (residue A x) (residue A y) := by
  have hA : W.toAffine.Equation x y := (W.toAffine.map_equation A.subtype_injective x y).mp h
  exact hA.map (residue A)

theorem Affine.nonsingular_residue (hΔ : (W.map (residue A)).Δ ≠ 0) {x y : A}
    (h : (W.map A.subtype).toAffine.Equation (x : L) (y : L)) :
    (W.map (residue A)).toAffine.Nonsingular (residue A x) (residue A y) :=
  (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).mp (Affine.equation_residue W h)

variable {W}

open Classical in

noncomputable def reducePoint (hΔ : (W.map (residue A)).Δ ≠ 0) :
    (W.map A.subtype).toAffine.Point → (W.map (residue A)).toAffine.Point
  | .zero => .zero
  | .some x y h =>
    if hx : x ∈ A then
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1)
    else
      .zero

variable (hΔ : (W.map (residue A)).Δ ≠ 0)

@[simp]
lemma reducePoint_zero : reducePoint hΔ (0 : (W.map A.subtype).toAffine.Point) = 0 :=
  rfl

lemma reducePoint_some_of_mem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∈ A) :
    reducePoint hΔ (.some x y h) =
      .some (residue A ⟨x, hx⟩) (residue A ⟨y, Affine.Y_mem_of_X_mem W h.1 hx⟩)
        (Affine.nonsingular_residue W hΔ h.1) := by
  simp only [reducePoint]
  exact dif_pos hx

lemma reducePoint_some_of_notMem {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (hx : x ∉ A) : reducePoint hΔ (.some x y h) = 0 := by
  simp only [reducePoint]
  exact dif_neg hx

theorem reducePoint_neg (P : (W.map A.subtype).toAffine.Point) :
    reducePoint hΔ (-P) = -reducePoint hΔ P := by
  cases P with
  | zero => rfl
  | some x y h =>
    rw [Affine.Point.neg_some]
    by_cases hx : x ∈ A
    · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
      rw [reducePoint_some_of_mem _ _ hx, reducePoint_some_of_mem _ _ hx,
        Affine.Point.neg_some]
      refine some_congr rfl ?_ _ _

      show residue A (W.toAffine.negY ⟨x, hx⟩ ⟨y, hy⟩) = _
      exact (Affine.map_negY (residue A) (⟨x, hx⟩ : A) (⟨y, hy⟩ : A)).symm
    · rw [reducePoint_some_of_notMem _ _ hx, reducePoint_some_of_notMem _ _ hx]
      rfl

section Inertia

open scoped Pointwise

variable (K : Type*) [Field K] [Algebra K L]

theorem _root_.ValuationSubring.smul_mem_of_mem_decompositionSubgroup {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K) {z : L} (hz : z ∈ A) : σ z ∈ A := by
  have h1 : σ • z ∈ σ • A := ValuationSubring.smul_mem_pointwise_smul σ z A hz
  rwa [MulAction.mem_stabilizer_iff.mp hσ, AlgEquiv.smul_def] at h1

variable {K}

theorem _root_.ValuationSubring.residue_smul_eq_of_mem_inertiaSubgroup
    {σ : L ≃ₐ[K] L} (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K) (a : A) :
    residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a) = residue A a := by
  have h1 : MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
      ⟨σ, hσ⟩ = 1 := hσI
  calc residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • a)
      = (⟨σ, hσ⟩ : A.decompositionSubgroup K) • residue A a := rfl
    _ = MulSemiringAction.toRingAut (A.decompositionSubgroup K) (ResidueField A)
          ⟨σ, hσ⟩ (residue A a) := rfl
    _ = residue A a := by rw [h1]; rfl

theorem reducePoint_some_apply_of_mem_inertia {σ : L ≃ₐ[K] L}
    (hσ : σ ∈ A.decompositionSubgroup K)
    (hσI : (⟨σ, hσ⟩ : A.decompositionSubgroup K) ∈ A.inertiaSubgroup K)
    {x y : L} (h : (W.map A.subtype).toAffine.Nonsingular x y)
    (h' : (W.map A.subtype).toAffine.Nonsingular (σ x) (σ y)) :
    reducePoint hΔ (.some (σ x) (σ y) h') = reducePoint hΔ (.some x y h) := by
  by_cases hx : x ∈ A
  · have hy : y ∈ A := Affine.Y_mem_of_X_mem W h.1 hx
    have hσx : σ x ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hx
    have hσy : σ y ∈ A := A.smul_mem_of_mem_decompositionSubgroup K hσ hy
    rw [reducePoint_some_of_mem _ _ hσx, reducePoint_some_of_mem _ _ hx]

    refine some_congr ?_ ?_ _ _
    · calc residue A (⟨σ x, hσx⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨x, hx⟩ : A)) := rfl
        _ = residue A (⟨x, hx⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
    · calc residue A (⟨σ y, hσy⟩ : A)
          = residue A ((⟨σ, hσ⟩ : A.decompositionSubgroup K) • (⟨y, hy⟩ : A)) := rfl
        _ = residue A (⟨y, hy⟩ : A) := A.residue_smul_eq_of_mem_inertiaSubgroup hσ hσI _
  · have hσx : σ x ∉ A := fun hmem => hx (by
      simpa using A.smul_mem_of_mem_decompositionSubgroup K (inv_mem hσ) hmem)
    rw [reducePoint_some_of_notMem _ _ hσx, reducePoint_some_of_notMem _ _ hx]

end Inertia

end WeierstrassCurve
