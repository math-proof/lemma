import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

noncomputable abbrev ρ {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (k : K) : K ⊗[F] P →ₗ[K] K ⊗[F] P :=
  LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F)
private lemma ρ_tmul {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (k x : K) (v : P) : ρ k (x ⊗ₜ[F] v) = x ⊗ₜ[F] (k • v) := by
  simp [ρ, LinearMap.baseChange_tmul]
private lemma ρ_add_apply {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (b₁ b₂ : K) (m : K ⊗[F] P) : ρ (b₁ + b₂) m = ρ b₁ m + ρ b₂ m := by
  refine TensorProduct.inductionOn m ?_ ?_
  ·
    intro x v
    rw [ρ_tmul, ρ_tmul, ρ_tmul, add_smul, TensorProduct.tmul_add]
  ·
    intro m₁ m₂ h₁ h₂
    rw [map_add, map_add, map_add, h₁, h₂]
    abel
private lemma ρ_smul_apply {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (c : F) (b : K) (m : K ⊗[F] P) : ρ (c • b) m = c • ρ b m := by
  refine TensorProduct.inductionOn m ?_ ?_
  ·
    intro x v
    rw [ρ_tmul, ρ_tmul, smul_assoc, TensorProduct.tmul_smul]
  ·
    intro m₁ m₂ h₁ h₂
    rw [map_add, map_add, h₁, h₂, smul_add]
private lemma ρ_mul_apply {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (b x : K) (m : K ⊗[F] P) : ρ (b * x) m = ρ b (ρ x m) := by
  refine TensorProduct.inductionOn m ?_ ?_
  ·
    intro y v
    rw [ρ_tmul, ρ_tmul, ρ_tmul, mul_smul]
  ·
    intro m₁ m₂ h₁ h₂
    rw [map_add, map_add, map_add, h₁, h₂]
private lemma ρ_comm_apply {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (b x : K) (m : K ⊗[F] P) : ρ b (ρ x m) = ρ x (ρ b m) := by
  rw [← ρ_mul_apply, ← ρ_mul_apply, mul_comm]
private noncomputable def actBil {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] : K →ₗ[F] K →ₗ[F] (K ⊗[F] P →ₗ[F] K ⊗[F] P) :=
  LinearMap.mk₂ F (fun a b => (a • ρ b).restrictScalars F) (fun a₁ a₂ b => LinearMap.ext fun m => by simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.add_apply, add_smul]) (fun c a b => LinearMap.ext fun m => by simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, smul_assoc]) (fun a b₁ b₂ => LinearMap.ext fun m => by simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, LinearMap.add_apply, ρ_add_apply, smul_add]) (fun c a b => LinearMap.ext fun m => by simp only [LinearMap.restrictScalars_apply, LinearMap.smul_apply, ρ_smul_apply]; rw [smul_comm])
private noncomputable def act {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] : K ⊗[F] K →ₗ[F] (K ⊗[F] P →ₗ[F] K ⊗[F] P) :=
  TensorProduct.lift actBil
private lemma act_tmul {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (a b : K) (m : K ⊗[F] P) : act (a ⊗ₜ[F] b) m = a • ρ b m := by
  simp [act, actBil]
private lemma act_smul_left {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (r : K ⊗[F] K) (x : K) (m : K ⊗[F] P) : act r (x • m) = x • act r m := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a b
    rw [act_tmul, act_tmul, map_smul, smul_comm]
  ·
    intro r₁ r₂ h₁ h₂
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂, smul_add]
private lemma act_ρ {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (r : K ⊗[F] K) (x : K) (m : K ⊗[F] P) : act r (ρ x m) = ρ x (act r m) := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a b
    rw [act_tmul, act_tmul, map_smul, ρ_comm_apply]
  ·
    intro r₁ r₂ h₁ h₂
    rw [map_add, LinearMap.add_apply, LinearMap.add_apply, h₁, h₂, map_add]
private lemma act_tmul_one_mul {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (x : K) (r : K ⊗[F] K) (m : K ⊗[F] P) : act ((x ⊗ₜ[F] (1 : K)) * r) m = x • act r m := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, act_tmul, act_tmul, mul_smul]
  ·
    intro r₁ r₂ h₁ h₂
    rw [mul_add, map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply, smul_add]
private lemma act_one_tmul_mul {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (x : K) (r : K ⊗[F] K) (m : K ⊗[F] P) : act (((1 : K) ⊗ₜ[F] x) * r) m = ρ x (act r m) := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a b
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul, act_tmul, act_tmul, ρ_mul_apply, map_smul]
  ·
    intro r₁ r₂ h₁ h₂
    rw [mul_add, map_add, LinearMap.add_apply, h₁, h₂, map_add, LinearMap.add_apply, map_add]
private lemma act_eq_lmul_smul_of_diag {F K P : Type u} [Field F] [Field K] [Algebra F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P] (w : K ⊗[F] P) (hw : ∀ k : K, k • w = ρ k w) (r : K ⊗[F] K) : act r w = (Algebra.TensorProduct.lmul' F (S := K) r) • w := by
  refine TensorProduct.inductionOn r ?_ ?_
  ·
    intro a b
    rw [act_tmul, ← hw b, ← mul_smul, Algebra.TensorProduct.lmul'_apply_tmul]
  ·
    intro r₁ r₂ h₁ h₂
    rw [map_add, LinearMap.add_apply, h₁, h₂, map_add, add_smul]
/--
[TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_TensorProduct_mulMap_injOn_and_surjOn_diagonal_of_isSeparable.lean)
-/
@[path]
private lemma main
  {F K P : Type u} [Field F] [Field K] [Algebra F K] [FiniteDimensional F K] [Algebra.IsSeparable F K] [AddCommGroup P] [Module K P] [Module F P] [IsScalarTower F K P]
  (π : K ⊗[F] P →ₗ[K] P)
  -- given
  (hπ : ∀ (a : K) (v : P), π (a ⊗ₜ[F] v) = a • v) :
  -- imply
  (∀ w : K ⊗[F] P, (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) → π w = 0 → w = 0) ∧ ∀ v : P, ∃ w : K ⊗[F] P, (∀ k : K, k • w = LinearMap.baseChange K ((LinearMap.lsmul K P k).restrictScalars F) w) ∧ π w = v := by
  -- proof
  let _ : Algebra.FormallyUnramified F K := Algebra.FormallyUnramified.of_isSeparable F K
  obtain ⟨t, ht1, ht2⟩ := (Algebra.FormallyUnramified.iff_exists_tensorProduct (R := F) (S := K)).mp inferInstance
  have hkey : ∀ x : K, ((x ⊗ₜ[F] (1 : K)) * t) = (((1 : K) ⊗ₜ[F] x) * t) := by
    intro x
    have := ht1 x
    rw [sub_mul, sub_eq_zero] at this
    apply this.symm
  change (∀ w : K ⊗[F] P, (∀ k : K, k • w = ρ k w) → π w = 0 → w = 0) ∧ ∀ v : P, ∃ w : K ⊗[F] P, (∀ k : K, k • w = ρ k w) ∧ π w = v
  have hπρ : ∀ (b : K) (m : K ⊗[F] P), π (ρ b m) = b • π m := by
    intro b m
    refine TensorProduct.inductionOn m ?_ ?_
    ·
      intro x v
      rw [ρ_tmul, hπ, hπ, smul_comm]
    ·
      intro m₁ m₂ h₁ h₂
      rw [map_add, map_add, h₁, h₂, map_add, smul_add]
  have hπact : ∀ (r : K ⊗[F] K) (m : K ⊗[F] P), π (act r m) = (Algebra.TensorProduct.lmul' F (S := K) r) • π m := by
    intro r m
    refine TensorProduct.inductionOn r ?_ ?_
    ·
      intro a b
      rw [act_tmul, map_smul, hπρ, ← mul_smul, Algebra.TensorProduct.lmul'_apply_tmul]
    ·
      intro r₁ r₂ h₁ h₂
      rw [map_add, LinearMap.add_apply, map_add, h₁, h₂, map_add, add_smul]
  have hT : ∀ m : K ⊗[F] P, act t m = act t ((1 : K) ⊗ₜ[F] π m) := by
    intro m
    refine TensorProduct.inductionOn m ?_ ?_
    ·
      intro x v
      calc
        _ = act t (x • ((1 : K) ⊗ₜ[F] v)) := by rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
        _ = act ((x ⊗ₜ[F] (1 : K)) * t) ((1 : K) ⊗ₜ[F] v) := by rw [act_tmul_one_mul, act_smul_left]
        _ = act (((1 : K) ⊗ₜ[F] x) * t) ((1 : K) ⊗ₜ[F] v) := by rw [hkey]
        _ = act t (ρ x ((1 : K) ⊗ₜ[F] v)) := by rw [act_one_tmul_mul, act_ρ]
        _ = act t ((1 : K) ⊗ₜ[F] π (x ⊗ₜ[F] v)) := by rw [ρ_tmul, hπ]
    ·
      intro m₁ m₂ h₁ h₂
      rw [map_add, h₁, h₂, ← map_add, ← TensorProduct.tmul_add, ← map_add]
  constructor
  ·
    intro w hw hπw
    have h1 : act t w = w := by rw [act_eq_lmul_smul_of_diag w hw t, ht2, one_smul]
    rw [← h1, hT w, hπw, TensorProduct.tmul_zero, map_zero]
  ·
    intro v
    refine ⟨act t ((1 : K) ⊗ₜ[F] v), fun k => ?_, ?_⟩
    · rw [← act_tmul_one_mul, hkey, act_one_tmul_mul]
    · rw [hπact, ht2, one_smul, hπ, one_smul]


-- created on 2026-10-20
