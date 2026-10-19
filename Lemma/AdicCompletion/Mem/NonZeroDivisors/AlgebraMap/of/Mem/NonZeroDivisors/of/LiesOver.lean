import Mathlib
import Lemma.AdicCompletion.exists.RingEquiv.of.IsLocalization.AtPrime.of.IsMaximal

open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 800000

namespace BDescN1

open scoped TensorProduct

theorem exists_injective_linearMap_pi {R : Type*} [CommRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [NoZeroSMulDivisors R M] :
    ∃ (n : ℕ) (ψ : M →ₗ[R] (Fin n → R)), Function.Injective ψ := by
  classical
  let K := FractionRing R
  let N := K ⊗[R] M
  let ι : M →ₗ[R] N := TensorProduct.mk R K M 1
  have hι : Function.Injective ι := by
    rw [IsLocalizedModule.injective_iff_isRegular (S := nonZeroDivisors R) (f := ι)]
    rintro ⟨c, hc⟩
    have hc0 : c ≠ 0 := nonZeroDivisors.ne_zero hc
    intro m m' h
    have h' : c • m = c • m' := h
    rw [← sub_eq_zero, ← smul_sub, smul_eq_zero] at h'
    exact sub_eq_zero.mp (h'.resolve_left hc0)
  have : Module.Finite K N := inferInstance
  let n := Module.finrank K N
  let b := Module.finBasis K N
  let e : N ≃ₗ[K] (Fin n → K) := b.equivFun
  let φ : M →ₗ[R] (Fin n → K) := (e.toLinearMap.restrictScalars R).comp ι
  have hφ : Function.Injective φ := e.injective.comp hι
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin (R := R) (M := M)
  obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors R)
    (fun ji : Fin k × Fin n => φ (s ji.1) ji.2)
  let W : Submodule R (Fin n → K) :=
    { carrier := {v | ∀ i, IsLocalization.IsInteger R ((d : R) • v i)}
      add_mem' := fun {v w} hv hw i => by
        simp only [Pi.add_apply, smul_add]; exact IsLocalization.isInteger_add (hv i) (hw i)
      zero_mem' := fun i => by simp only [Pi.zero_apply, smul_zero]; exact IsLocalization.isInteger_zero
      smul_mem' := fun a {v} hv i => by
        rw [Pi.smul_apply, smul_comm (d : R) a (v i)]; exact IsLocalization.isInteger_smul (hv i) }
  have hW : ∀ m : M, φ m ∈ W := by
    intro m
    have hm : m ∈ Submodule.span R (Set.range s) := by rw [hs]; trivial
    have : Submodule.span R (Set.range s) ≤ W.comap φ := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact fun i => hd ⟨j, i⟩
    exact this hm
  have hinj : Function.Injective (algebraMap R K) := IsFractionRing.injective R K
  choose c hc using fun (m : M) (i : Fin n) => hW m i
  refine ⟨n, { toFun := fun m i => c m i, map_add' := ?_, map_smul' := ?_ }, ?_⟩
  · intro x y; funext i; apply hinj
    rw [hc, map_add φ, Pi.add_apply, smul_add, Pi.add_apply, map_add (algebraMap R K), hc, hc]
  · intro a x; funext i; apply hinj
    rw [hc, LinearMap.map_smul, Pi.smul_apply, smul_comm (d : R) a, RingHom.id_apply, Pi.smul_apply,
      smul_eq_mul, map_mul, hc, Algebra.smul_def]
  · intro x y hxy
    apply hφ
    funext i
    have h1 : algebraMap R K (c x i) = algebraMap R K (c y i) := by
      have := congrFun hxy i; exact congrArg (algebraMap R K) this
    rw [hc, hc] at h1
    have hd0 : (algebraMap R K (d : R)) ≠ 0 :=
      IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
    rw [Algebra.smul_def, Algebra.smul_def] at h1
    exact mul_left_cancel₀ hd0 h1

theorem smul_eq_zero_of_mem_nonZeroDivisors_of_flat {R : Type*} [CommRing R] [IsDomain R]
    (M : Type*) [AddCommGroup M] [Module R M] [Module.Finite R M] [NoZeroSMulDivisors R M]
    (R' : Type*) [CommRing R'] [Algebra R R'] [Module.Flat R R']
    {r : R'} (hr : r ∈ nonZeroDivisors R') {z : R' ⊗[R] M} (hz : r • z = 0) : z = 0 := by
  classical
  obtain ⟨n, ψ, hψ⟩ := exists_injective_linearMap_pi (R := R) M
  let f : R' ⊗[R] M →ₗ[R'] R' ⊗[R] (Fin n → R) := ψ.baseChange R'
  have hf : Function.Injective f := Module.Flat.lTensor_preserves_injective_linearMap (M := R') ψ hψ
  let g : R' ⊗[R] (Fin n → R) ≃ₗ[R'] (Fin n → R') := TensorProduct.piScalarRight R R' R' (Fin n)
  apply hf
  apply g.injective
  rw [map_zero, map_zero]
  have h1 : r • g (f z) = 0 := by rw [← map_smul, ← map_smul, hz, map_zero, map_zero]
  funext i
  have h2 : r * g (f z) i = 0 := by
    have := congrFun h1 i
    rwa [Pi.smul_apply, smul_eq_mul] at this
  exact (mem_nonZeroDivisors_iff.mp hr).1 _ h2

end BDescN1

/--
[AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AdicCompletion_mem_nonZeroDivisors_algebraMap_of_mem_nonZeroDivisors_of_liesOver.lean)
-/
@[path]
private lemma main
  {O : Type} [CommRing O] [IsNoetherianRing O] [IsLocalRing O] {C : Type} [CommRing C] [IsDomain C] [Algebra O C] [Module.Finite O C] [FaithfulSMul O C]
-- given
  (𝔫 : Ideal C) [𝔫.IsMaximal] [𝔫.LiesOver (maximalIdeal O)] :
-- imply
  ∀ r : AdicCompletion (maximalIdeal O) O, r ∈ nonZeroDivisors (AdicCompletion (maximalIdeal O) O) →
      algebraMap (AdicCompletion (maximalIdeal O) O) (AdicCompletion 𝔫 C) r ∈ nonZeroDivisors (AdicCompletion 𝔫 C) := by
-- proof
  classical
  have : IsNoetherianRing C := IsNoetherianRing.of_finite O C
  set 𝔪 := maximalIdeal O with h𝔪
  set I : Ideal C := 𝔪.map (algebraMap O C) with hI
  have hI𝔫 : I ≤ 𝔫 := by
    rw [hI, Ideal.map_le_iff_le_comap]
    intro o ho
    have h := Ideal.LiesOver.over (P := 𝔫) (p := 𝔪)
    rw [h] at ho
    exact ho
  have : IsArtinianRing (C ⧸ I) := by
    let _ : Field (O ⧸ 𝔪) := Ideal.Quotient.field 𝔪
    have : Module.Finite (O ⧸ 𝔪) (C ⧸ I) := inferInstance
    exact IsArtinianRing.of_finite (O ⧸ 𝔪) (C ⧸ I)
  let Φ := AdicCompletion.semilocalPiEquiv I
  let T := AdicCompletion.tensorRingEquiv C 𝔪
  have hT : ∀ (x : AdicCompletion 𝔪 O) (c : C), T (x ⊗ₜ[O] c) = AdicCompletion.completionBaseChangeHom C 𝔪 x * AdicCompletion.of I C c :=
    fun x c => AdicCompletion.tensorRingEquiv_tmul C 𝔪 x c
  let 𝔫' : {P : Ideal C // P.IsMaximal ∧ I ≤ P} := ⟨𝔫, inferInstance, hI𝔫⟩
  have hΦ : ∀ y, Φ y 𝔫' = AdicCompletion.semilocalComponent I hI𝔫 y :=
    fun y => AdicCompletion.semilocalPiEquiv_apply I hI𝔫 y

  have hcompat : ∀ x : AdicCompletion 𝔪 O, AdicCompletion.semilocalComponent I hI𝔫 (AdicCompletion.completionBaseChangeHom C 𝔪 x)
      = algebraMap (AdicCompletion 𝔪 O) (AdicCompletion 𝔫 C) x :=
    fun x => AdicCompletion.semilocalComponent_completionBaseChangeHom_eq_algebraMap 𝔪 𝔫 (hI ▸ hI𝔫) x
  have : NoZeroSMulDivisors O C := by
    refine ⟨fun {o c} h => ?_⟩
    rw [Algebra.smul_def, mul_eq_zero] at h
    rcases h with h | h
    · left; exact (faithfulSMul_iff_algebraMap_injective O C).mp inferInstance (by rw [h, map_zero])
    · right; exact h
  have : IsDomain O := Function.Injective.isDomain (algebraMap O C) ((faithfulSMul_iff_algebraMap_injective O C).mp inferInstance)
  have : Module.Flat O (AdicCompletion 𝔪 O) := inferInstance
  intro r hr
  have key : ∀ x : AdicCompletion 𝔫 C, algebraMap (AdicCompletion 𝔪 O) (AdicCompletion 𝔫 C) r * x = 0 → x = 0 := by
    intro x hx
    let x0 : ∀ P : {P : Ideal C // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal C) C := Function.update (0 : ∀ P : {P : Ideal C // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal C) C) 𝔫' x
    let X := Φ.symm x0
    have hX : Φ X = x0 := Φ.apply_symm_apply _
    have h1 : Φ (AdicCompletion.completionBaseChangeHom C 𝔪 r * X) = 0 := by
      funext P
      rw [map_mul, Pi.mul_apply, hX, Pi.zero_apply]
      if hP : P = 𝔫' then
        subst hP
        show Φ _ 𝔫' * Function.update (0 : ∀ P : {P : Ideal C // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal C) C) 𝔫' x 𝔫' = 0
        rw [Function.update_self, hΦ, hcompat]; exact hx
      else
        show Φ _ P * Function.update (0 : ∀ P : {P : Ideal C // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal C) C) 𝔫' x P = 0
        rw [Function.update_of_ne hP, Pi.zero_apply, mul_zero]
    have h2 : AdicCompletion.completionBaseChangeHom C 𝔪 r * X = 0 := Φ.injective (by rw [h1, map_zero])
    have hsm : ∀ z : AdicCompletion 𝔪 O ⊗[O] C, r • z = (r ⊗ₜ[O] (1 : C)) * z := by
      intro z
      induction z using TensorProduct.inductionOn with
      | tmul a c => rw [TensorProduct.smul_tmul', Algebra.TensorProduct.tmul_mul_tmul, one_mul, smul_eq_mul]
      | add x y hx hy => rw [smul_add, mul_add, hx, hy]
    have hof1 : AdicCompletion.of I C (1 : C) = 1 := by
      have := (AdicCompletion.algebraMap_apply I (R := C) (S := C) (1 : C)).symm
      rw [Algebra.algebraMap_self, RingHom.id_apply] at this
      rw [this, map_one]
    have h3 : r • T.symm X = 0 := by
      apply T.injective
      rw [hsm, map_mul, hT, hof1, mul_one, AlgEquiv.apply_symm_apply, h2, map_zero]
    have h4 : T.symm X = 0 :=
      BDescN1.smul_eq_zero_of_mem_nonZeroDivisors_of_flat C (AdicCompletion 𝔪 O) hr h3
    have h5 : X = 0 := by
      have := congrArg T h4
      rwa [AlgEquiv.apply_symm_apply, map_zero] at this
    have h6 : x0 = 0 := by rw [← hX, h5, map_zero]
    have := congrFun h6 𝔫'
    change Function.update (0 : ∀ P : {P : Ideal C // P.IsMaximal ∧ I ≤ P}, AdicCompletion (P : Ideal C) C) 𝔫' x 𝔫' = 0 at this
    rwa [Function.update_self] at this
  exact mem_nonZeroDivisors_iff.mpr ⟨key, fun x hx => key x (by rwa [mul_comm] at hx)⟩

-- created on 2026-10-09
