import Mathlib
import sympy.Basic
open scoped TensorProduct


/--
[Algebra_adjoin_div_tensorProduct_bijective_of_flat](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_adjoin_div_tensorProduct_bijective_of_flat.lean)
-/
@[path]
private lemma main
  [CommRing C]
  [CommRing S] [Algebra C S]
  [CommRing C'] [Algebra C C'] [Module.Flat C C']
  [CommRing S'] [Algebra C' S'] [Algebra C S'] [IsScalarTower C C' S']
  {a : C} [IsLocalization.Away a S] [IsLocalization.Away (algebraMap C C' a) S']
  {I : Ideal C}
  {φ : S →ₐ[C] S'} :
-- imply
  let B : Subalgebra C S := Algebra.adjoin C {x : S | ∃ i ∈ I, x * algebraMap C S a = algebraMap C S i}
  let B' : Subalgebra C' S' :=
    Algebra.adjoin C' {x : S' | ∃ i ∈ I.map (algebraMap C C'),
      x * algebraMap C' S' (algebraMap C C' a) = algebraMap C' S' i}
  let θ : C' ⊗[C] ↥B →ₐ[C'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId C' S') (φ.comp B.val) (fun _ _ => Commute.all _ _)
  Function.Injective θ ∧ ∀ x : S', x ∈ Set.range θ ↔ x ∈ B' := by
-- proof
  intro B B' θ
  classical
  have hφC : ∀ c : C, φ (algebraMap C S c) = algebraMap C' S' (algebraMap C C' c) := by
    intro c
    rw [φ.commutes, IsScalarTower.algebraMap_apply C C' S']
  have hθ : ∀ (c' : C') (b : ↥B), θ (c' ⊗ₜ[C] b) = algebraMap C' S' c' * φ (b : S) :=
    fun c' b => Algebra.TensorProduct.lift_tmul _ _ _ c' b
  obtain ⟨u, hu⟩ := (IsLocalization.Away.algebraMap_isUnit (S := S') (algebraMap C C' a))
  let ψ : C' ⊗[C] S →ₐ[C'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId C' S') φ (fun _ _ => Commute.all _ _)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) (C' ⊗[C] S) :=
    IsLocalization.tensor S (Submonoid.powers a)
  let _ : IsLocalization (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) S' := inferInstance
  have hψ : ∀ (c' : C') (s : S), ψ (c' ⊗ₜ[C] s) = algebraMap C' S' c' * φ s :=
    fun c' s => Algebra.TensorProduct.lift_tmul _ _ _ c' s
  let e : C' ⊗[C] S ≃ₐ[C'] S' :=
    IsLocalization.algEquiv (Algebra.algebraMapSubmonoid C' (Submonoid.powers a)) _ _
  have hψe : ψ = e.toAlgHom :=
    (IsLocalization.algHom_subsingleton (Algebra.algebraMapSubmonoid C' (Submonoid.powers a))).elim _ _
  have hψbij : Function.Bijective ψ := by
    rw [hψe]
    apply e.bijective
  let ι : C' ⊗[C] ↥B →ₐ[C'] C' ⊗[C] S := Algebra.TensorProduct.map (AlgHom.id C' C') B.val
  have hθfac : ∀ t, θ t = ψ (ι t) := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c' b =>
      rw [hθ, show ι (c' ⊗ₜ[C] b) = c' ⊗ₜ[C] (b : S) from rfl]
      apply (hψ c' (b : S)).symm
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add, map_add]
  have hιlin : ∀ t, ι t = (B.val.toLinearMap.lTensor C') t := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c' b =>
      rfl
    | add x y hx hy =>
      rw [map_add, hx, hy, map_add]
  have hιinj : Function.Injective ι := by
    have : (ι : C' ⊗[C] ↥B → C' ⊗[C] S) = (B.val.toLinearMap.lTensor C') := funext hιlin
    rw [this]
    apply Module.Flat.lTensor_preserves_injective_linearMap _ (fun x y h => Subtype.ext h)
  have hinj : Function.Injective θ := by
    have : (θ : C' ⊗[C] ↥B → S') = ψ ∘ ι := funext hθfac
    rw [this]
    apply hψbij.1.comp hιinj
  have hgen : ∀ x : S, (∃ i ∈ I, x * algebraMap C S a = algebraMap C S i) → φ x ∈ B' := by
    rintro x ⟨i, hi, hx⟩
    apply Algebra.subset_adjoin
    refine ⟨algebraMap C C' i, Ideal.mem_map_of_mem _ hi, ?_⟩
    calc
      _ = φ x * φ (algebraMap C S a) := by
        rw [hφC]
      _ = φ (x * algebraMap C S a) := (map_mul φ _ _).symm
      _ = φ (algebraMap C S i) := by
        rw [hx]
      _ = algebraMap C' S' (algebraMap C C' i) := hφC i
  have hφB : ∀ y : S, y ∈ B → φ y ∈ B' := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx =>
      apply hgen x hx
    | algebraMap c =>
      rw [hφC]
      apply Subalgebra.algebraMap_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      apply add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      apply mul_mem hx hy
  have hsub : ∀ t : C' ⊗[C] ↥B, θ t ∈ B' := by
    intro t
    induction t using TensorProduct.inductionOn with
    | tmul c' b =>
      rw [hθ]
      apply mul_mem (Subalgebra.algebraMap_mem _ _) (hφB _ b.2)
    | add x y hx hy =>
      rw [map_add]
      apply add_mem hx hy
  have hcore : ∀ i' : C', i' ∈ I.map (algebraMap C C') → algebraMap C' S' i' * ↑u⁻¹ ∈ Set.range θ := by
    intro i' hi'
    induction hi' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨i, hi, rfl⟩ := hz
      let xi : S := algebraMap C S i * IsLocalization.Away.invSelf a
      have hxi : xi * algebraMap C S a = algebraMap C S i := by
        show algebraMap C S i * IsLocalization.Away.invSelf a * algebraMap C S a = algebraMap C S i
        rw [mul_assoc, mul_comm (IsLocalization.Away.invSelf a), IsLocalization.Away.mul_invSelf, mul_one]
      have hxiB : xi ∈ B := Algebra.subset_adjoin ⟨i, hi, hxi⟩
      refine ⟨(1 : C') ⊗ₜ[C] ⟨xi, hxiB⟩, ?_⟩
      show θ ((1 : C') ⊗ₜ[C] ⟨xi, hxiB⟩) = _
      rw [hθ, map_one, one_mul, Units.eq_mul_inv_iff_mul_eq, hu]
      calc
        _ = φ xi * φ (algebraMap C S a) := by
          rw [hφC]
        _ = φ (xi * algebraMap C S a) := (map_mul φ _ _).symm
        _ = φ (algebraMap C S i) := by
          rw [hxi]
        _ = algebraMap C' S' (algebraMap C C' i) := hφC i
    | zero =>
      refine ⟨0, ?_⟩
      rw [map_zero, map_zero, zero_mul]
    | add z w _ _ hz hw =>
      obtain ⟨tz, htz⟩ := hz
      obtain ⟨tw, htw⟩ := hw
      refine ⟨tz + tw, ?_⟩
      rw [map_add, htz, htw, map_add, add_mul]
    | smul c z _ hz =>
      obtain ⟨tz, htz⟩ := hz
      refine ⟨c • tz, ?_⟩
      rw [map_smul, htz, smul_eq_mul, map_mul, Algebra.smul_def, mul_assoc]
  have hsup : ∀ x : S', x ∈ B' → x ∈ Set.range θ := by
    intro x hx
    have hR : (θ.range : Set S') = Set.range θ := rfl
    rw [← hR]
    refine Algebra.adjoin_le ?_ hx
    rintro y ⟨i', hi', hy⟩
    have hy' : y = algebraMap C' S' i' * ↑u⁻¹ := by
      rw [Units.eq_mul_inv_iff_mul_eq, hu]
      apply hy
    rw [hy']
    apply hcore i' hi'
  refine ⟨hinj, fun x => ⟨fun ⟨t, ht⟩ => ht ▸ hsub t, hsup x⟩⟩


-- created on 2026-10-13
