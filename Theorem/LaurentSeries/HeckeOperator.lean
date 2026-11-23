module

public import Theorem.Scheme.Correspondence
public import Theorem.LaurentSeries.ArithmeticGalois

public noncomputable section

set_option autoImplicit false

noncomputable section

open IsDedekindDomain

namespace ModularCurve

open AlgebraicCurve IntermediateField HahnSeries

section PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]

public theorem coeffMap_qExpand' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (n : ℕ)
    [NeZero n] (x : LaurentSeries R) : coeffMap f (qExpand R n x) = qExpand S n (coeffMap f x) := by
  ext k
  by_cases hk : (n : ℤ) ∣ k
  · obtain ⟨m, rfl⟩ := hk
    rw [coeffMap_coeff, qExpand_coeff_mul, qExpand_coeff_mul, coeffMap_coeff]
  · rw [coeffMap_coeff, qExpand_coeff_of_not_dvd n _ hk, qExpand_coeff_of_not_dvd n _ hk,
      map_zero]


public theorem coeffEmb_qExpand' (L : Type*) [Field L] [Algebra ℚ L] (n : ℕ) [NeZero n]
    (x : LaurentSeries ℚ) : coeffEmb L (qExpand ℚ n x) = qExpand L n (coeffEmb L x) :=
  coeffMap_qExpand' _ n x

variable (L) in

public theorem laurentBaseChange_mono' {F₀ F₁ : IntermediateField ℚ (LaurentSeries ℚ)}
    (h : F₀ ≤ F₁) : laurentBaseChange L F₀ ≤ laurentBaseChange L F₁ := by
  rw [laurentBaseChange, IntermediateField.adjoin_le_iff]
  rintro _ ⟨y, hy, rfl⟩
  exact coeffEmb_mem_laurentBaseChange L (h hy)


public theorem qExpand_mem_laurentBaseChange' {F₀ : IntermediateField ℚ (LaurentSeries ℚ)} (n : ℕ)
    [NeZero n] {F₁ : IntermediateField ℚ (LaurentSeries ℚ)} (hF : ∀ y ∈ F₀, qExpand ℚ n y ∈ F₁)
    {x : LaurentSeries L} (hx : x ∈ laurentBaseChange L F₀) :
    qExpand L n x ∈ laurentBaseChange L F₁ := by
  rw [mem_laurentBaseChange_iff] at hx
  induction hx using Subfield.closure_induction with
  | mem y hy =>
      rcases hy with ⟨a, rfl⟩ | ⟨z, hz, rfl⟩
      · rw [algebraMap_laurentSeries_eq_single, qExpand_single, mul_zero,
          ← algebraMap_laurentSeries_eq_single]
        exact (laurentBaseChange L F₁).algebraMap_mem _
      · rw [← coeffEmb_qExpand']
        exact coeffEmb_mem_laurentBaseChange L (hF z hz)
  | one => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | neg x _ hx => simpa using neg_mem hx
  | inv x _ hx => simpa using inv_mem hx
  | mul x y _ _ hx hy => simpa using mul_mem hx hy

end PrivateSupply

variable {L : Type*} [Field L] [Algebra ℚ L]
variable (N ℓ : ℕ) [NeZero N] [NeZero ℓ]

section DegeneracyMapsBar

variable (L) in


@[simp]
public theorem coe_heckeAlphaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeAlphaBar L N ℓ x : LaurentSeries L) = (x : LaurentSeries L) :=
  IntermediateField.coe_inclusion _ x

variable (L) in


@[simp]
public theorem coe_heckeBetaBarRingHom (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBarRingHom L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

variable (L) in


public theorem heckeAlphaBar_eq_inclusion
    (h : laurentBaseChange L (modularFunctionFieldFull N)
      ≤ laurentBaseChange L (modularFunctionFieldFull (N * ℓ))) :
    heckeAlphaBar L N ℓ = IntermediateField.inclusion h :=
  rfl

omit [NeZero N] in

@[simp]
public theorem coe_heckeBetaBar (x : laurentBaseChange L (modularFunctionFieldFull N)) :
    (heckeBetaBar L N ℓ x : LaurentSeries L) = qExpand L ℓ (x : LaurentSeries L) :=
  rfl

end DegeneracyMapsBar

section HeckePic0Bar

variable (L) in

