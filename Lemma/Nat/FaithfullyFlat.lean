import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


/--
[Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_FaithfullyFlat_of_isAdicComplete_of_forall_pow_maximalIdeal.lean)
-/
@[path]
private lemma main
  (R B : Type*) [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
  [CommRing B] [IsLocalRing B] [IsAdicComplete (maximalIdeal B) B]
  [Algebra R B] [IsLocalHom (algebraMap R B)]
  -- given
  (hinj : ∀ (n : ℕ) (r : R), algebraMap R B r ∈ maximalIdeal B ^ n → r ∈ maximalIdeal R ^ n)
  (hsurj : ∀ (n : ℕ) (b : B), ∃ r : R, b - algebraMap R B r ∈ maximalIdeal B ^ n) :
  -- imply
  Module.FaithfullyFlat R B := by
  -- proof
  classical
  set mR := maximalIdeal R with hmR
  set mB := maximalIdeal B with hmB
  have hloc : ∀ r : R, r ∈ mR → algebraMap R B r ∈ mB := by
    intro r hr
    by_contra h
    have : IsUnit (algebraMap R B r) := IsLocalRing.notMem_maximalIdeal.mp h
    apply (hmR ▸ hr : r ∈ maximalIdeal R) (IsLocalHom.map_nonunit r this)
  have hmapPow : ∀ (n : ℕ) (r : R), r ∈ mR ^ n → algebraMap R B r ∈ mB ^ n := by
    intro n r hr
    have : (mR ^ n).map (algebraMap R B) ≤ mB ^ n := by
      rw [Ideal.map_pow]
      apply Ideal.pow_right_mono (Ideal.map_le_iff_le_comap.mpr fun r hr => Ideal.mem_comap.mpr (hloc r hr)) n
    apply this (Ideal.mem_map_of_mem _ hr)
  have smodR : ∀ (n : ℕ) (r : R), r ∈ (mR ^ n • ⊤ : Submodule R R) ↔ r ∈ mR ^ n := by
    intro n r
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  have smodB : ∀ (n : ℕ) (b : B), b ∈ (mB ^ n • ⊤ : Submodule B B) ↔ b ∈ mB ^ n := by
    intro n b
    rw [Ideal.smul_eq_mul, Ideal.mul_top]
  choose ρ hρ using fun n b => hsurj n b
  have key : ∀ (n : ℕ) (b : B) (r r' : R), b - algebraMap R B r ∈ mB ^ n → b - algebraMap R B r' ∈ mB ^ n →
      (Submodule.Quotient.mk r : R ⧸ (mR ^ n • ⊤ : Submodule R R)) = Submodule.Quotient.mk r' := by
    intro n b r r' h h'
    rw [Submodule.Quotient.eq, smodR]
    apply hinj
    rw [map_sub]
    have : algebraMap R B r - algebraMap R B r' = (b - algebraMap R B r') - (b - algebraMap R B r) := by ring
    rw [this]
    apply Ideal.sub_mem _ h' h
  let ψ : ∀ n : ℕ, B →ₗ[R] R ⧸ (mR ^ n • ⊤ : Submodule R R) := fun n =>
    { toFun := fun b => Submodule.Quotient.mk (ρ n b)
      map_add' := fun b b' => by
        rw [← Submodule.Quotient.mk_add]
        apply key n (b + b') _ _ (hρ n (b + b'))
        rw [map_add]
        have : b + b' - (algebraMap R B (ρ n b) + algebraMap R B (ρ n b')) =
            (b - algebraMap R B (ρ n b)) + (b' - algebraMap R B (ρ n b')) := by ring
        rw [this]
        apply Ideal.add_mem _ (hρ n b) (hρ n b')
      map_smul' := fun r b => by
        rw [RingHom.id_apply, ← Submodule.Quotient.mk_smul]
        apply key n (r • b) _ _ (hρ n (r • b))
        rw [smul_eq_mul, map_mul, Algebra.smul_def, ← mul_sub]
        apply Ideal.mul_mem_left _ _ (hρ n b) }
  have hψ : ∀ (n : ℕ) (b : B), ψ n b = Submodule.Quotient.mk (ρ n b) := fun n b => rfl
  have hcompat : ∀ {m n : ℕ} (hle : m ≤ n),
      LinearMap.comp (AdicCompletion.transitionMap mR R hle) (ψ n) = ψ m := by
    intro m n hle
    ext b
    rw [LinearMap.comp_apply, hψ, hψ]
    show Submodule.Quotient.mk (ρ n b) = Submodule.Quotient.mk (ρ m b)
    apply key m b _ _ (Ideal.pow_le_pow_right hle (hρ n b)) (hρ m b)
  let Ψ : B →ₗ[R] AdicCompletion mR R := AdicCompletion.lift mR ψ hcompat
  have hΨ : ∀ (b : B) (n : ℕ), (Ψ b).val n = Submodule.Quotient.mk (ρ n b) := fun b n => rfl
  have hinjΨ : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro b hb
    rw [LinearMap.mem_ker] at hb
    apply IsHausdorff.haus (IsAdicComplete.toIsHausdorff : IsHausdorff mB B) b
    intro n
    rw [SModEq.zero, smodB]
    have h0 : (Ψ b).val n = 0 := by
      rw [hb]
      rfl
    rw [hΨ, Submodule.Quotient.mk_eq_zero, smodR] at h0
    have : b = (b - algebraMap R B (ρ n b)) + algebraMap R B (ρ n b) := by ring
    rw [this]
    apply Ideal.add_mem _ (hρ n b) (hmapPow n _ h0)
  have hsurjΨ : Function.Surjective Ψ := by
    intro x
    obtain ⟨f, rfl⟩ := AdicCompletion.mk_surjective mR R x
    have hcau : ∀ {m n : ℕ}, m ≤ n → algebraMap R B (f m) ≡ algebraMap R B (f n) [SMOD (mB ^ m • ⊤ : Submodule B B)] := by
      intro m n hle
      rw [SModEq.sub_mem, smodB, ← map_sub]
      apply hmapPow
      have := f.property hle
      rwa [SModEq.sub_mem, smodR] at this
    obtain ⟨L, hL⟩ := IsPrecomplete.prec (IsAdicComplete.toIsPrecomplete : IsPrecomplete mB B) @hcau
    refine ⟨L, ?_⟩
    ext n
    rw [hΨ, AdicCompletion.mk_apply_coe]
    show Submodule.Quotient.mk (ρ n L) = Submodule.Quotient.mk (f n)
    apply key n L _ _ (hρ n L)
    have := (hL n).symm
    rwa [SModEq.sub_mem, smodB] at this
  let e : B ≃ₗ[R] AdicCompletion mR R := LinearEquiv.ofBijective Ψ ⟨hinjΨ, hsurjΨ⟩
  let _ : Module.Flat R B := Module.Flat.of_linearEquiv e
  refine (Module.FaithfullyFlat.iff_flat_and_proper_ideal R B).mpr ⟨inferInstance, fun I hI => ?_⟩
  intro htop
  have hle : I ≤ mR := le_maximalIdeal hI
  have h1 : (1 : B) ∈ I • (⊤ : Submodule R B) := by
    rw [htop]
    apply Submodule.mem_top
  have : I • (⊤ : Submodule R B) ≤ mB.restrictScalars R := by
    rw [Ideal.smul_top_eq_map]
    intro b hb
    apply (Ideal.map_le_iff_le_comap.mpr (fun r hr => Ideal.mem_comap.mpr (hloc r (hle hr)))) hb
  apply (Ideal.ne_top_iff_one _).mp (maximalIdeal.isMaximal B).ne_top (this h1)


-- created on 2026-10-20
-- updated on 2026-10-28
