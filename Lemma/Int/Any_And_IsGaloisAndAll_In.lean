import Mathlib
import Initialize.Tactic.Attr.Basic
open IntermediateField


private noncomputable def factorHom
  {K : Type*} [Field K] {I : Type u} [DecidableEq I] {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
  {Ω : Type*} [Field Ω] [Algebra K Ω]
  (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I) (hi : φ (Pi.single i 1) = 1) : Ai i →ₐ[K] Ω where
  toFun a := by
    exact φ (Pi.single i a)
  map_one' := by
    exact hi
  map_mul' a b := by
    rw [← map_mul, ← Pi.single_mul]
  map_zero' := by
    rw [Pi.single_zero, map_zero]
  map_add' a b := by
    rw [← map_add, ← Pi.single_add]
  commutes' k := by
    rw [Algebra.algebraMap_eq_smul_one, show (Pi.single i (k • (1 : Ai i)) : Π j, Ai j) =
        k • Pi.single i (1 : Ai i) from Pi.single_smul i k (1 : Ai i), map_smul, hi,
      Algebra.algebraMap_eq_smul_one]


private lemma factorHom_apply
  [Field K] [Field Ω] [Algebra K Ω]
  {I : Type u} [DecidableEq I]
  {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
  (φ : (Π i, Ai i) →ₐ[K] Ω) (i : I) (hi : φ (Pi.single i 1) = 1) (a : Ai i) :
-- imply
  factorHom φ i hi a = φ (Pi.single i a) := rfl


private lemma exists_eq_comp_evalAlgHom
  [Field K] [Field Ω] [Algebra K Ω]
  {I : Type u} [Finite I]
  {Ai : I → Type u} [∀ i, Field (Ai i)] [∀ i, Algebra K (Ai i)]
  (φ : (Π i, Ai i) →ₐ[K] Ω) :
-- imply
  ∃ (i : I) (ψ : Ai i →ₐ[K] Ω), ∀ x, φ x = ψ (x i) := by
-- proof
  classical
  obtain ⟨_⟩ := nonempty_fintype I
  have hsum : ∑ i, φ (Pi.single i (1 : Ai i)) = 1 := by
    rw [← map_sum, Finset.univ_sum_single (fun _ => (1 : _))]
    apply map_one φ
  have hex : ∃ i, φ (Pi.single i (1 : Ai i)) ≠ 0 := by
    by_contra h
    push Not at h
    rw [Finset.sum_eq_zero (fun i _ => h i)] at hsum
    apply zero_ne_one hsum
  obtain ⟨i, hi0⟩ := hex
  have hidem : φ (Pi.single i (1 : Ai i)) * φ (Pi.single i (1 : Ai i)) = φ (Pi.single i (1 : Ai i)) := by
    rw [← map_mul, ← Pi.single_mul, mul_one]
  have hi : φ (Pi.single i (1 : Ai i)) = 1 := by
    have h := hidem
    rwa [mul_left_eq_self₀, or_iff_left hi0] at h
  refine ⟨i, factorHom φ i hi, fun x => ?_⟩
  rw [factorHom_apply]
  have hx : x = Pi.single i (x i) + x * (1 - Pi.single i 1) := by
    ext j
    if hj : j = i then
      subst hj
      simp
    else
      simp [hj]
  conv_lhs => rw [hx]
  rw [map_add, map_mul, map_sub, map_one, hi, sub_self, mul_zero, add_zero]


/--
[Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_FormallyUnramified_exists_isGalois_forall_algHom_apply_mem.lean)
-/
@[path]
private lemma main
  {K E : Type u} [Field K] [CommRing E] [Algebra K E] [Module.Finite K E] [Algebra.FormallyUnramified K E] [Field Ω] [Algebra K Ω] [Normal K Ω] :
-- imply
  ∃ L : IntermediateField K Ω, FiniteDimensional K L ∧ IsGalois K L ∧ ∀ (φ : E →ₐ[K] Ω) (e : E), φ e ∈ L := by
-- proof
  classical
  have : Algebra.FormallyEtale K E := Algebra.FormallyEtale.of_formallyUnramified_of_field K E
  obtain ⟨I, hI, Ai, hF, hA, iso, hsep⟩ := (Algebra.FormallyEtale.iff_exists_algEquiv_prod K E).mp inferInstance
  have : ∀ i, FiniteDimensional K (Ai i) := fun i =>
    Module.Finite.of_surjective ((LinearMap.proj i).comp iso.toLinearMap) ((Function.surjective_eval i).comp iso.surjective)
  let N : I → IntermediateField K Ω := fun i => normalClosure K (Ai i) Ω
  refine ⟨⨆ i, N i, ?_, ?_, ?_⟩
  · apply finiteDimensional_iSup_of_finite
  ·
    have : Normal K (⨆ i, N i : IntermediateField K Ω) := normal_iSup (F := K) (K := Ω) N
    have : ∀ i, Algebra.IsSeparable K (N i) := by
      intro i
      rw [← le_separableClosure_iff]
      refine (normalClosure_le_iff).mpr fun ψ => ?_
      rintro _ ⟨a, rfl⟩
      rw [mem_separableClosure_iff]
      change IsSeparable K (ψ a)
      rw [IsSeparable, minpoly.algHom_eq ψ ψ.injective]
      apply Algebra.IsSeparable.isSeparable K a
    have : Algebra.IsSeparable K (⨆ i, N i : IntermediateField K Ω) := isSeparable_iSup K Ω
    refine ⟨⟩
  ·
    intro φ e
    obtain ⟨i, ψ, hψ⟩ := exists_eq_comp_evalAlgHom (φ.comp iso.symm.toAlgHom)
    have hφ : φ e = ψ (iso e i) := by
      have h := hψ (iso e)
      simpa using h
    rw [hφ]
    apply le_iSup N i
    apply AlgHom.fieldRange_le_normalClosure ψ ⟨iso e i, rfl⟩


-- created on 2026-10-13
