import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


private lemma natCard_algHom_eq_finrank
  {K : Type u} [Field K] [IsAlgClosed K]
  {L : Type u} [CommRing L] [Algebra K L] [Module.Finite K L] [IsReduced L] :
  Nat.card (L →ₐ[K] K) = Module.finrank K L := by
  classical
  have : IsArtinianRing L := IsArtinianRing.of_finite K L
  have : Fintype (MaximalSpectrum L) := Fintype.ofFinite _
  let e : L ≃ₐ[K] ∀ I : MaximalSpectrum L, L ⧸ I.asIdeal := (IsArtinianRing.equivPi L).restrictScalars K
  have hbij : ∀ I : MaximalSpectrum L, Function.Bijective (algebraMap K (L ⧸ I.asIdeal)) := by
    intro I
    have : Algebra.IsIntegral K (L ⧸ I.asIdeal) := Algebra.IsIntegral.of_finite K _
    apply IsAlgClosed.algebraMap_bijective_of_isIntegral
  have hrank : Module.finrank K L = Fintype.card (MaximalSpectrum L) := by
    rw [e.toLinearEquiv.finrank_eq, Module.finrank_pi_fintype]
    have : ∀ I : MaximalSpectrum L, Module.finrank K (L ⧸ I.asIdeal) = 1 := by
      intro I
      have := (LinearEquiv.ofBijective (Algebra.linearMap K (L ⧸ I.asIdeal)) (hbij I)).finrank_eq
      rw [Module.finrank_self] at this
      apply this.symm
    simp [this]
  let ρ : ∀ I : MaximalSpectrum L, (L ⧸ I.asIdeal) ≃ₐ[K] K := fun I =>
    (AlgEquiv.ofBijective (Algebra.ofId K (L ⧸ I.asIdeal)) (hbij I)).symm
  let toHom : MaximalSpectrum L → (L →ₐ[K] K) := fun I =>
    ((ρ I : (L ⧸ I.asIdeal) →ₐ[K] K)).comp (Ideal.Quotient.mkₐ K I.asIdeal)
  have hker : ∀ I : MaximalSpectrum L, RingHom.ker (toHom I) = I.asIdeal := by
    intro I
    ext x
    simp only [toHom, RingHom.mem_ker, AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk,
      EmbeddingLike.map_eq_zero_iff, AlgEquiv.coe_toAlgHom]
    apply Ideal.Quotient.eq_zero_iff_mem
  have hinj : Function.Injective toHom := by
    intro I J h
    apply MaximalSpectrum.ext
    rw [← hker I, ← hker J, h]
  have hsurj : Function.Surjective toHom := by
    intro φ
    have hmax : (RingHom.ker φ).IsMaximal := by
      apply RingHom.ker_isMaximal_of_surjective
      intro k
      exact ⟨algebraMap K L k, φ.commutes k⟩
    refine ⟨⟨RingHom.ker φ, hmax⟩, ?_⟩
    apply AlgHom.ext
    intro x
    set I : MaximalSpectrum L := ⟨RingHom.ker φ, hmax⟩
    obtain ⟨k, hk⟩ := (hbij I).2 (Ideal.Quotient.mk I.asIdeal x)
    have hx : x - algebraMap K L k ∈ RingHom.ker φ := by
      change x - algebraMap K L k ∈ I.asIdeal
      rw [← Ideal.Quotient.eq, ← hk]
      rfl
    have h1 : φ x = k := by
      have := hx
      rwa [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    have h2 : toHom I x = k := by
      have hx' : x - algebraMap K L k ∈ RingHom.ker (toHom I) := by
        rwa [hker]
      rwa [RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at hx'
    rw [h2, h1]
  rw [hrank, ← Nat.card_eq_fintype_card]
  apply (Nat.card_congr (Equiv.ofBijective toHom ⟨hinj, hsurj⟩)).symm


/--
[Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_natCard_algHom_eq_finrank_residueField_tensorProduct_of_flat_of_isReduced.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] [IsDomain R] [ValuationRing R]
  {K : Type u} [Field K] [Algebra R K] [IsFractionRing R K] [IsAlgClosed K]
  {B : Type u} [CommRing B] [Algebra R B] [Module.Finite R B] [Module.Flat R B] [IsReduced (K ⊗[R] B)] :
-- imply
  Nat.card (B →ₐ[R] K) =
    Module.finrank (IsLocalRing.ResidueField R) (IsLocalRing.ResidueField R ⊗[R] B) := by
-- proof
  classical
  have : Module.Free R B := Module.free_of_flat_of_isLocalRing
  rw [Module.finrank_baseChange, ← Module.finrank_baseChange (R := K),
    Nat.card_congr (AlgHom.liftEquiv R K B K)]
  apply natCard_algHom_eq_finrank (K := K) (L := K ⊗[R] B)


-- created on 2026-10-13
