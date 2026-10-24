import Mathlib
import sympy.Basic
open Polynomial Algebra IsCyclotomicExtension


/-- ported from external source -/

private lemma  isIntegral_aeval_int {L : Type v} [CommRing L] {ζ : L} (hζi : IsIntegral ℤ ζ) (g : ℤ[X]) : IsIntegral ℤ (aeval ζ g) := by
  have hmem : aeval ζ g ∈ Algebra.adjoin ℤ ({ζ} : Set L) := Polynomial.aeval_mem_adjoin_singleton ℤ ζ
  have : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ ({ζ} : Set L)) :=
    Algebra.IsIntegral.adjoin (fun x hx => by rwa [Set.mem_singleton_iff.mp hx])
  have h : IsIntegral ℤ (⟨aeval ζ g, hmem⟩ : Algebra.adjoin ℤ ({ζ} : Set L)) := Algebra.IsIntegral.isIntegral _
  refine h.map (Algebra.adjoin ℤ ({ζ} : Set L)).val

private lemma  prod_embeddings_aeval_eq {K : Type u} {L : Type v} [Field K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
  [IsCyclotomicExtension {n} K L] [FiniteDimensional K L] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K))
  (E : Type*) [Field E] [Algebra K E] (g : ℤ[X]) :
  (∏ σ : L →ₐ[K] E, σ (aeval ζ g)) = ∏ μ ∈ primitiveRoots n E, aeval μ g := by
  classical
  let e := hζ.embeddingsEquivPrimitiveRoots E hirr
  rw [← Finset.prod_coe_sort (primitiveRoots n E)]
  refine Fintype.prod_equiv e _ _ fun σ => ?_
  rw [IsPrimitiveRoot.embeddingsEquivPrimitiveRoots_apply_coe]
  show σ.toRingHom.toIntAlgHom (aeval ζ g) = _
  rw [← Polynomial.aeval_algHom_apply]
  rfl

private lemma  exists_int_norm_aeval {K : Type u} {L : Type v} [Field K] [CharZero K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
  [IsCyclotomicExtension {n} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K))
  (L₀ : Type) [Field L₀] [Algebra ℚ L₀] [IsCyclotomicExtension {n} ℚ L₀] {ζ₀ : L₀} (hζ₀ : IsPrimitiveRoot ζ₀ n) (g : ℤ[X]) :
  ∃ D : ℤ, algebraMap ℤ K D = Algebra.norm K (aeval ζ g) ∧
    algebraMap ℤ ℚ D = Algebra.norm ℚ (aeval ζ₀ g) := by
  classical
  have : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {n} K L
  have : Algebra.IsSeparable K L := IsCyclotomicExtension.isSeparable {n} K L
  have hirr₀ : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat (NeZero.pos n)
  have : FiniteDimensional ℚ L₀ := IsCyclotomicExtension.finiteDimensional {n} ℚ L₀
  have : Algebra.IsSeparable ℚ L₀ := IsCyclotomicExtension.isSeparable {n} ℚ L₀
  have hint : IsIntegral ℤ (Algebra.norm ℚ (aeval ζ₀ g)) :=
    Algebra.isIntegral_norm ℚ (isIntegral_aeval_int (hζ₀.isIntegral (NeZero.pos n)) g)
  obtain ⟨D, hD⟩ := IsIntegrallyClosed.isIntegral_iff.mp hint
  refine ⟨D, ?_, hD⟩
  let E := AlgebraicClosure L
  have : CharZero E := charZero_of_injective_algebraMap (algebraMap K E).injective
  apply (algebraMap K E).injective
  have h1 : algebraMap K E (Algebra.norm K (aeval ζ g)) = ∏ μ ∈ primitiveRoots n E, aeval μ g := by
    rw [Algebra.norm_eq_prod_embeddings K E]
    convert prod_embeddings_aeval_eq hζ hirr E g <;> first | rfl | exact Subsingleton.elim _ _
  have h2 : algebraMap ℚ E (Algebra.norm ℚ (aeval ζ₀ g)) = ∏ μ ∈ primitiveRoots n E, aeval μ g := by
    rw [Algebra.norm_eq_prod_embeddings ℚ E]
    convert prod_embeddings_aeval_eq hζ₀ hirr₀ E g <;> first | rfl | exact Subsingleton.elim _ _
  rw [h1, ← h2, ← hD, eq_intCast, eq_intCast, map_intCast, map_intCast]

private lemma  exists_int_dvd_pow_totient_and_algebraMap_eq_discr
  {K : Type u} {L : Type v} [Field K] [CharZero K] [Field L] [Algebra K L] {n : ℕ} [NeZero n]
  [IsCyclotomicExtension {n} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K)) :
  ∃ D : ℤ, D ∣ (n : ℤ) ^ n.totient ∧
    algebraMap ℤ K D = Algebra.discr K (fun i : Fin (hζ.powerBasis K).dim => (hζ.powerBasis K).gen ^ (i : ℕ)) := by
  classical
  have : FiniteDimensional K L := IsCyclotomicExtension.finiteDimensional {n} K L
  have : Algebra.IsSeparable K L := IsCyclotomicExtension.isSeparable {n} K L
  have hn : 0 < n := NeZero.pos n
  let L₀ := CyclotomicField n ℚ
  have hcyc : IsCyclotomicExtension {n} ℚ L₀ := CyclotomicField.isCyclotomicExtension n ℚ
  let ζ₀ : L₀ := zeta n ℚ L₀
  have hζ₀ : IsPrimitiveRoot ζ₀ n := zeta_spec n ℚ L₀
  have hirr₀ : Irreducible (cyclotomic n ℚ) := cyclotomic.irreducible_rat hn
  have : FiniteDimensional ℚ L₀ := IsCyclotomicExtension.finiteDimensional {n} ℚ L₀
  have : Algebra.IsSeparable ℚ L₀ := IsCyclotomicExtension.isSeparable {n} ℚ L₀
  set Φ := cyclotomic n ℤ with hΦ
  set g₁ := derivative Φ with hg₁
  set g₂ := ∏ d ∈ n.properDivisors, cyclotomic d ℤ with hg₂
  have hprod : g₂ * Φ = X ^ n - 1 := by
    rw [hg₂, hΦ, mul_comm, ← prod_cyclotomic_eq_X_pow_sub_one hn ℤ, ← Nat.cons_self_properDivisors hn.ne', Finset.prod_cons]
  have hder : derivative g₂ * Φ + g₂ * g₁ = C (n : ℤ) * X ^ (n - 1) := by
    rw [hg₁, ← derivative_mul, hprod, derivative_sub, derivative_X_pow, derivative_one, sub_zero]
  have hΦζ₀ : aeval ζ₀ Φ = 0 := by
    have h := hζ₀.isRoot_cyclotomic hn
    rwa [IsRoot.def, ← map_cyclotomic_int n L₀, eval_map, ← algebraMap_int_eq, ← aeval_def] at h
  have key₀ : aeval ζ₀ g₂ * aeval ζ₀ g₁ = (n : L₀) * ζ₀ ^ (n - 1) := by
    have h := congrArg (aeval ζ₀) hder
    rwa [map_add, map_mul, map_mul, hΦζ₀, mul_zero, zero_add, map_mul, aeval_C, aeval_X_pow, map_natCast] at h
  obtain ⟨D₁, hD₁K, hD₁ℚ⟩ := exists_int_norm_aeval hζ hirr L₀ hζ₀ g₁
  obtain ⟨D₂, -, hD₂ℚ⟩ := exists_int_norm_aeval hζ hirr L₀ hζ₀ g₂
  obtain ⟨D₀, -, hD₀ℚ⟩ := exists_int_norm_aeval hζ hirr L₀ hζ₀ X
  rw [aeval_X] at hD₀ℚ
  have hfin₀ : Module.finrank ℚ L₀ = n.totient := IsCyclotomicExtension.finrank L₀ hirr₀
  have hcast : ∀ D : ℤ, (D : ℚ) = algebraMap ℤ ℚ D := fun D => (eq_intCast _ _).symm
  have hnormrel : Algebra.norm ℚ (aeval ζ₀ g₂) * Algebra.norm ℚ (aeval ζ₀ g₁) = (n : ℚ) ^ n.totient * Algebra.norm ℚ ζ₀ ^ (n - 1) := by
    have h := congrArg (Algebra.norm ℚ) key₀
    rw [map_mul, map_mul, map_pow] at h
    rw [h, ← hfin₀]
    congr 1
    have : (n : L₀) = algebraMap ℚ L₀ (n : ℚ) := by rw [map_natCast]
    rw [this, Algebra.norm_algebraMap]
  have hrel : D₂ * D₁ = (n : ℤ) ^ n.totient * D₀ ^ (n - 1) := by
    apply Int.cast_injective (α := ℚ)
    rwa [Int.cast_mul, Int.cast_mul, Int.cast_pow, Int.cast_pow, Int.cast_natCast, hcast, hcast, hcast, hD₂ℚ, hD₁ℚ, hD₀ℚ]
  have hD₀u : IsUnit D₀ := by
    have h1 : (D₀ : ℚ) ^ n = 1 := by
      rw [hcast, hD₀ℚ, ← map_pow, hζ₀.pow_eq_one, map_one]
    have h2 : D₀ ^ n = 1 := by exact_mod_cast h1
    refine IsUnit.of_pow_eq_one h2 hn.ne'
  have hdvd : D₁ ∣ (n : ℤ) ^ n.totient := by
    have : D₁ ∣ (n : ℤ) ^ n.totient * D₀ ^ (n - 1) := ⟨D₂, by rw [← hrel, mul_comm]⟩
    exact (IsUnit.dvd_mul_right (hD₀u.pow _)).mp this
  have hdisc : Algebra.discr K (fun i : Fin (hζ.powerBasis K).dim => (hζ.powerBasis K).gen ^ (i : ℕ)) =
      (-1) ^ (n.totient * (n.totient - 1) / 2) * algebraMap ℤ K D₁ := by
    rw [← PowerBasis.coe_basis, Algebra.discr_powerBasis_eq_norm, IsCyclotomicExtension.finrank L hirr, hD₁K]
    congr 2
    rw [IsPrimitiveRoot.powerBasis_gen, ← hζ.minpoly_eq_cyclotomic_of_irreducible hirr, ← map_cyclotomic_int,
      derivative_map, ← algebraMap_int_eq, aeval_map_algebraMap]
  refine ⟨(-1) ^ (n.totient * (n.totient - 1) / 2) * D₁, ?_, ?_⟩
  · exact (IsUnit.mul_left_dvd (isUnit_one.neg.pow _)).mpr hdvd
  · rw [hdisc, map_mul, map_pow, map_neg, map_one]

private lemma  exists_unit_algebraMap_eq_discr_powerBasis
  (R : Type*) [CommRing R] {K : Type u} {L : Type v} [Field K] [CharZero K] [Field L] [Algebra K L] [Algebra R K]
  {n : ℕ} [NeZero n] (hnu : IsUnit ((n : ℕ) : R))
  [IsCyclotomicExtension {n} K L] {ζ : L} (hζ : IsPrimitiveRoot ζ n) (hirr : Irreducible (cyclotomic n K)) :
  ∃ d : Rˣ, algebraMap R K (d : R) = Algebra.discr K (fun i : Fin (hζ.powerBasis K).dim => (hζ.powerBasis K).gen ^ (i : ℕ)) := by
  obtain ⟨D, hdvd, hD⟩ := exists_int_dvd_pow_totient_and_algebraMap_eq_discr hζ hirr
  have hu : IsUnit ((D : ℤ) : R) := by
    obtain ⟨c, hc⟩ := hdvd
    have : ((n : ℕ) : R) ^ n.totient = (D : R) * (c : R) := by exact_mod_cast congrArg (Int.cast : ℤ → R) hc
    exact isUnit_of_mul_isUnit_left (this ▸ hnu.pow _)
  refine ⟨hu.unit, ?_⟩
  rw [IsUnit.unit_spec, map_intCast, ← hD, eq_intCast]
@[path]
private lemma main
  {K : Type u} [Field K] [CharZero K]
  {L : Type v} [Field L] [Algebra K L]
  {n : ℕ} [NeZero n] [IsCyclotomicExtension {n} K L]
  {ζ : L}
-- given
  (hζ : IsPrimitiveRoot ζ n)
  (hirr : Irreducible (cyclotomic n K)) :
-- imply
  ∃ D : ℤ, D ∣ (n : ℤ) ^ n.totient ∧
      algebraMap ℤ K D = Algebra.discr K (fun i : Fin (hζ.powerBasis K).dim => (hζ.powerBasis K).gen ^ (i : ℕ)) :=
  exists_int_dvd_pow_totient_and_algebraMap_eq_discr hζ hirr


-- created on 2026-10-23
