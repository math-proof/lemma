import Mathlib
import sympy.Basic
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v w₁ w₂ w₁' w₂'

private lemma exists_apply_eq_of_baseChange_residueField {R : Type u} [CommRing R] {k : Type v} [Field k] [Algebra R k] {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk] (hπ : Function.Surjective (algebraMap R k)) (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k) (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk) (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n)) (y : k ⊗[R] M) : ∃ m : M, ∀ n : N, Bk (eM y) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n) := by
  refine TensorProduct.inductionOn y ?_ ?_
  ·
    intro a m
    obtain ⟨r, rfl⟩ := hπ a
    refine ⟨r • m, fun n => ?_⟩
    have h1 : (algebraMap R k r) ⊗ₜ[R] m = (algebraMap R k r) • ((1 : k) ⊗ₜ[R] m) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [h1, map_smul, map_smul, LinearMap.smul_apply, hcomp, LinearMap.map_smul, LinearMap.smul_apply, smul_eq_mul, smul_eq_mul, map_mul]
  ·
    intro y z hy hz
    obtain ⟨m₁, h₁⟩ := hy
    obtain ⟨m₂, h₂⟩ := hz
    exact ⟨m₁ + m₂, fun n => by rw [map_add, map_add, LinearMap.add_apply, h₁ n, h₂ n, map_add, LinearMap.add_apply, map_add]⟩
private lemma surjective_of_baseChange_residueField {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k] {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk] [Module.Free R N] [Module.Finite R N] (hπ : Function.Surjective (algebraMap R k)) (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k) (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk) (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n)) (hBk : Function.Surjective Bk) : Function.Surjective B := by
  classical
  have hker : RingHom.ker (algebraMap R k) = IsLocalRing.maximalIdeal R := IsLocalRing.eq_maximalIdeal (RingHom.ker_isMaximal_of_surjective (algebraMap R k) hπ)
  let bN := Module.Free.chooseBasis R N
  let bNk : Module.Basis _ k Nk := (Algebra.TensorProduct.basis k bN).map eN
  have hbNk : ∀ j, bNk j = eN (1 ⊗ₜ[R] bN j) := fun j => by
    rw [Module.Basis.map_apply, Algebra.TensorProduct.basis_apply]
  have step : ∀ φ : N →ₗ[R] R, ∃ m : M, φ - B m ∈ (IsLocalRing.maximalIdeal R) • (⊤ : Submodule R (N →ₗ[R] R)) := by
    intro φ
    let g : Nk →ₗ[k] k := bNk.constr k fun j => algebraMap R k (φ (bN j))
    have hg : ∀ j, g (bNk j) = algebraMap R k (φ (bN j)) := fun j => Module.Basis.constr_basis bNk k _ j
    obtain ⟨x, hx⟩ := hBk g
    obtain ⟨y, rfl⟩ := eM.surjective x
    obtain ⟨m, hm⟩ := exists_apply_eq_of_baseChange_residueField hπ B Bk eM eN hcomp y
    refine ⟨m, ?_⟩
    have hcoord : ∀ j, (φ - B m) (bN j) ∈ IsLocalRing.maximalIdeal R := fun j => by
      rw [← hker, RingHom.mem_ker, LinearMap.sub_apply, map_sub, ← hm (bN j), hx, ← hbNk, hg, sub_self]
    rw [← Module.Basis.sum_dual_apply_smul_coord bN (φ - B m)]
    apply Submodule.sum_mem _ fun j _ => Submodule.smul_mem_smul (hcoord j) Submodule.mem_top
  have hle : (⊤ : Submodule R (N →ₗ[R] R)) ≤ LinearMap.range B ⊔ (IsLocalRing.maximalIdeal R) • ⊤ := by
    intro φ _
    obtain ⟨m, hm⟩ := step φ
    have : φ = B m + (φ - B m) := by abel
    rw [this]
    apply Submodule.add_mem_sup (LinearMap.mem_range_self _ _) hm
  apply LinearMap.range_eq_top.mp
  apply top_le_iff.mp
  apply Submodule.le_of_le_smul_of_le_jacobson_bot Module.Finite.fg_top (IsLocalRing.maximalIdeal_le_jacobson _) hle
private lemma finrank_eq_of_baseChange_residueField {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k] {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk] [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N] (Bk : Mk →ₗ[k] Nk →ₗ[k] k) (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk) (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) : Module.finrank R M = Module.finrank R N := by
  let _ : Module.Finite k Mk := Module.Finite.equiv eM
  let _ : Module.Finite k Nk := Module.Finite.equiv eN
  have hM : Module.finrank R M = Module.finrank k Mk := (Module.finrank_baseChange (R := k) (S := R) (M' := M)).symm.trans eM.finrank_eq
  have hN : Module.finrank R N = Module.finrank k Nk := (Module.finrank_baseChange (R := k) (S := R) (M' := N)).symm.trans eN.finrank_eq
  have h1 : Module.finrank k Mk ≤ Module.finrank k Nk := (LinearMap.finrank_le_finrank_of_injective hBk.1.injective).trans (Subspace.dual_finrank_eq).le
  have h2 : Module.finrank k Nk ≤ Module.finrank k Mk := (LinearMap.finrank_le_finrank_of_injective hBk.2.injective).trans (Subspace.dual_finrank_eq).le
  omega
private lemma bijective_and_flip_bijective_of_baseChange_residueField {R : Type u} [CommRing R] [IsLocalRing R] {k : Type v} [Field k] [Algebra R k] {M : Type w₁} {N : Type w₂} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N] {Mk : Type w₁'} {Nk : Type w₂'} [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk] [Module.Free R M] [Module.Finite R M] [Module.Free R N] [Module.Finite R N] (hπ : Function.Surjective (algebraMap R k)) (B : M →ₗ[R] N →ₗ[R] R) (Bk : Mk →ₗ[k] Nk →ₗ[k] k) (eM : k ⊗[R] M ≃ₗ[k] Mk) (eN : k ⊗[R] N ≃ₗ[k] Nk) (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n)) (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) : Function.Bijective B ∧ Function.Bijective B.flip := by
  classical
  have hsurj : Function.Surjective B := surjective_of_baseChange_residueField hπ B Bk eM eN hcomp hBk.1.surjective
  have hcompFlip : ∀ n m, Bk.flip (eN (1 ⊗ₜ[R] n)) (eM (1 ⊗ₜ[R] m)) = algebraMap R k (B.flip n m) := by
    intro n m
    rw [LinearMap.flip_apply, LinearMap.flip_apply]
    apply hcomp m n
  have hsurj' : Function.Surjective B.flip := surjective_of_baseChange_residueField hπ B.flip Bk.flip eN eM hcompFlip hBk.2.surjective
  have hrk : Module.finrank R M = Module.finrank R N := finrank_eq_of_baseChange_residueField Bk eM eN hBk
  have hdN : Module.finrank R M = Module.finrank R (N →ₗ[R] R) := hrk.trans (Module.Free.chooseBasis R N).toDualEquiv.finrank_eq
  have hdM : Module.finrank R N = Module.finrank R (M →ₗ[R] R) := hrk.symm.trans (Module.Free.chooseBasis R M).toDualEquiv.finrank_eq
  let e : M ≃ₗ[R] (N →ₗ[R] R) := LinearEquiv.ofFinrankEq _ _ hdN
  let e' : N ≃ₗ[R] (M →ₗ[R] R) := LinearEquiv.ofFinrankEq _ _ hdM
  exact ⟨⟨OrzechProperty.injective_of_surjective_of_injective e.toLinearMap B e.injective hsurj, hsurj⟩, ⟨OrzechProperty.injective_of_surjective_of_injective e'.toLinearMap B.flip e'.injective hsurj', hsurj'⟩⟩
/--
[LinearMap_bijective_and_flip_bijective_of_baseChange_residueField](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_LinearMap_bijective_and_flip_bijective_of_baseChange_residueField.lean)
-/
@[path]
private lemma main
  {R : Type u} {k : Type v} {M : Type w₁} {N : Type w₂} {Mk : Type w₁'} {Nk : Type w₂'} [CommRing R] [IsLocalRing R] [Field k] [Algebra R k] [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M] [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N] [AddCommGroup Mk] [Module k Mk] [AddCommGroup Nk] [Module k Nk]
  (B : M →ₗ[R] N →ₗ[R] R)
  (Bk : Mk →ₗ[k] Nk →ₗ[k] k)
  (eM : k ⊗[R] M ≃ₗ[k] Mk)
  (eN : k ⊗[R] N ≃ₗ[k] Nk)
  -- given
  (hπ : Function.Surjective (algebraMap R k))
  (hcomp : ∀ m n, Bk (eM (1 ⊗ₜ[R] m)) (eN (1 ⊗ₜ[R] n)) = algebraMap R k (B m n))
  (hBk : Function.Bijective Bk ∧ Function.Bijective Bk.flip) :
  -- imply
  Function.Bijective B ∧ Function.Bijective B.flip :=
  bijective_and_flip_bijective_of_baseChange_residueField hπ B Bk eM eN hcomp hBk


-- created on 2026-10-20
