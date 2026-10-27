import Mathlib
import Initialize.Tactic.Attr.Basic
open scoped TensorProduct


/--
[Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_IsUnramifiedAt_baseChange_of_ne_maximalIdeal_of_map_maximalIdeal_eq.lean)
-/
@[path]
private lemma main
  [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R'] [CommRing S]
  [Algebra R R'] [Algebra R S] [Module.Finite R S]
-- given
  (hmax : Ideal.map (algebraMap R R') (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal R')
  (hS : ∀ (𝔮 : Ideal S) [𝔮.IsPrime], ¬ 𝔮.IsMaximal → Algebra.IsUnramifiedAt R 𝔮) :
-- imply
  ∀ (𝔔 : Ideal (R' ⊗[R] S)) [𝔔.IsPrime], ¬ 𝔔.IsMaximal → Algebra.IsUnramifiedAt R' 𝔔 := by
-- proof
  intro 𝔔 _ h𝔔
  classical
  let _ : Algebra S (R' ⊗[R] S) := Algebra.TensorProduct.rightAlgebra
  let 𝔮 : Ideal S := 𝔔.comap (algebraMap S (R' ⊗[R] S))
  have h𝔮p : 𝔮.IsPrime := Ideal.IsPrime.comap _
  have : Algebra.IsIntegral R S := Algebra.IsIntegral.of_finite R S
  have : Algebra.IsIntegral R' (R' ⊗[R] S) := Algebra.IsIntegral.of_finite R' (R' ⊗[R] S)
  have h𝔮 : ¬ 𝔮.IsMaximal := by
    intro hmaxq
    apply h𝔔
    have h1 : (𝔮.comap (algebraMap R S)).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal 𝔮
    have h2 : 𝔮.comap (algebraMap R S) = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal h1
    have h3 : IsLocalRing.maximalIdeal R' ≤ 𝔔.comap (algebraMap R' (R' ⊗[R] S)) := by
      rw [← hmax, Ideal.map_le_iff_le_comap, Ideal.comap_comap, ← IsScalarTower.algebraMap_eq R R' (R' ⊗[R] S),
        IsScalarTower.algebraMap_eq R S (R' ⊗[R] S), ← Ideal.comap_comap]
      apply h2.symm.le
    have hne : 𝔔.comap (algebraMap R' (R' ⊗[R] S)) ≠ ⊤ := Ideal.comap_ne_top _ (Ideal.IsPrime.ne_top ‹_›)
    have h4 : (𝔔.comap (algebraMap R' (R' ⊗[R] S))).IsMaximal := by
      rw [← (IsLocalRing.maximalIdeal.isMaximal R').eq_of_le hne h3]
      apply IsLocalRing.maximalIdeal.isMaximal R'
    refine Ideal.isMaximal_of_isIntegral_of_isMaximal_under 𝔔 h4
  have hq_unr : Algebra.IsUnramifiedAt R 𝔮 := hS 𝔮 h𝔮
  have hq' : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum S) ∉ Module.support S Ω[S⁄R] := by
    have : (⟨𝔮, h𝔮p⟩ : PrimeSpectrum S) ∈ Algebra.unramifiedLocus R S := hq_unr
    rwa [Algebra.unramifiedLocus_eq_compl_support] at this
  rw [Module.mem_support_iff_of_finite] at hq'
  obtain ⟨s, hs, hsq⟩ := SetLike.not_le_iff_exists.mp hq'
  change (⟨𝔔, ‹_›⟩ : PrimeSpectrum (R' ⊗[R] S)) ∈ Algebra.unramifiedLocus R' (R' ⊗[R] S)
  rw [Algebra.unramifiedLocus_eq_compl_support, Set.mem_compl_iff, ← (KaehlerDifferential.tensorKaehlerEquiv R R' S (R' ⊗[R] S)).support_eq,
    Module.mem_support_iff_of_finite]
  intro hle
  apply hsq
  have hann : algebraMap S (R' ⊗[R] S) s ∈ Module.annihilator (R' ⊗[R] S) ((R' ⊗[R] S) ⊗[S] Ω[S⁄R]) := by
    rw [Module.mem_annihilator]
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul b w =>
      rw [TensorProduct.smul_tmul', smul_eq_mul, ← Algebra.smul_def, TensorProduct.smul_tmul, Module.mem_annihilator.mp hs w, TensorProduct.tmul_zero]
    | add x y hx hy =>
      rw [smul_add, hx, hy, add_zero]
  have := hle hann
  simp at this
  apply this


-- created on 2026-10-13
