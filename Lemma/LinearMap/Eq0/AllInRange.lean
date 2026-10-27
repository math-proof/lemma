import Mathlib
import Initialize.Tactic.Attr.Basic
open IsLocalRing
open scoped TensorProduct
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma lTensor_liftQ_injective {R : Type*} [CommRing R] [IsLocalRing R] {A B C : Type*} [AddCommGroup A] [Module R A] [AddCommGroup B] [Module R B] [AddCommGroup C] [Module R C] (f : A →ₗ[R] B) (g : B →ₗ[R] C) (hgf : LinearMap.range f ≤ LinearMap.ker g) (hS : ∀ z : ResidueField R ⊗[R] B, g.lTensor (ResidueField R) z = 0 → z ∈ LinearMap.range (f.lTensor (ResidueField R))) : Function.Injective (((LinearMap.range f).liftQ g hgf).lTensor (ResidueField R)) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  obtain ⟨z, rfl⟩ := LinearMap.lTensor_surjective (ResidueField R) (Submodule.mkQ_surjective (LinearMap.range f)) w
  have h1 : ((LinearMap.range f).liftQ g hgf).lTensor (ResidueField R) (((LinearMap.range f).mkQ).lTensor (ResidueField R) z) = g.lTensor (ResidueField R) z := by
    rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp, Submodule.liftQ_mkQ]
  rw [h1] at hw
  obtain ⟨y, rfl⟩ := hS z hw
  rw [← LinearMap.comp_apply, ← LinearMap.lTensor_comp]
  have hq : LinearMap.comp ((LinearMap.range f).mkQ) f = 0 := LinearMap.ext fun a => (Submodule.Quotient.mk_eq_zero _).mpr (LinearMap.mem_range_self f a)
  rw [hq, LinearMap.lTensor_zero, LinearMap.zero_apply]
private lemma free_coker {R : Type*} [CommRing R] [IsLocalRing R] (K : ℕ → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)] (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, LinearMap.comp (δ (i + 1)) (δ i) = 0) (h0 : Function.Injective ((δ 0).lTensor (ResidueField R))) (hS : ∀ (i : ℕ) (z : ResidueField R ⊗[R] K (i + 1)), (δ (i + 1)).lTensor (ResidueField R) z = 0 → z ∈ LinearMap.range ((δ i).lTensor (ResidueField R))) (i : ℕ) : Module.Free R (K (i + 1) ⧸ LinearMap.range (δ i)) := by
  induction i
  ·
    apply Module.free_of_lTensor_residueField_injective (δ 0) (LinearMap.range (δ 0)).mkQ (Submodule.mkQ_surjective _) (LinearMap.exact_map_mkQ_range _) h0
  ·
    rename_i i ih
    have hle : LinearMap.range (δ i) ≤ LinearMap.ker (δ (i + 1)) := LinearMap.range_le_ker_iff.mpr (hdd i)
    let _ := ih
    refine Module.free_of_lTensor_residueField_injective ((LinearMap.range (δ i)).liftQ (δ (i + 1)) hle) (LinearMap.range (δ (i + 1))).mkQ (Submodule.mkQ_surjective _) ?_ (lTensor_liftQ_injective (δ i) (δ (i + 1)) hle (hS i))
    rw [LinearMap.exact_iff, Submodule.ker_mkQ, Submodule.range_liftQ]
private lemma helper_main {R : Type*} [CommRing R] [IsLocalRing R] (K : ℕ → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)] (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, LinearMap.comp (δ (i + 1)) (δ i) = 0) (h0 : Function.Injective ((δ 0).lTensor (ResidueField R))) (hS : ∀ (i : ℕ) (z : ResidueField R ⊗[R] K (i + 1)), (δ (i + 1)).lTensor (ResidueField R) z = 0 → z ∈ LinearMap.range ((δ i).lTensor (ResidueField R))) : (∀ z : K 0, δ 0 z = 0 → z = 0) ∧ ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by
  constructor
  ·
    obtain ⟨l', hl'⟩ := (split_injective_iff_lTensor_residueField_injective (δ 0)).mpr h0
    intro z hz
    have h := LinearMap.congr_fun hl' z
    rw [LinearMap.comp_apply, hz, map_zero, LinearMap.id_apply] at h
    apply h.symm
  ·
    intro i z hz
    have hle : LinearMap.range (δ i) ≤ LinearMap.ker (δ (i + 1)) := LinearMap.range_le_ker_iff.mpr (hdd i)
    let _ := free_coker K δ hdd h0 hS i
    obtain ⟨l', hl'⟩ := (split_injective_iff_lTensor_residueField_injective ((LinearMap.range (δ i)).liftQ (δ (i + 1)) hle)).mpr (lTensor_liftQ_injective (δ i) (δ (i + 1)) hle (hS i))
    apply (Submodule.Quotient.mk_eq_zero _).mp ((Function.LeftInverse.injective (g := l') fun x => LinearMap.congr_fun hl' x) _)
    rw [map_zero, Submodule.liftQ_apply]
    apply hz
/--
[Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_forall_eq_zero_and_mem_range_of_forall_baseChange_residueField_of_finite_free.lean)
-/
@[path]
private lemma main
  (R : Type*) [CommRing R] [IsLocalRing R] (n : ℕ)
  (K : ℕ → Type*) [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
  [∀ i, Module.Finite R (K i)] [∀ i, Module.Free R (K i)]
  (_ : ∀ i, n < i → Subsingleton (K i))
  (δ : ∀ i, K i →ₗ[R] K (i + 1)) (hdd : ∀ i, LinearMap.comp (δ (i + 1)) (δ i) = 0)
  (h0 : ∀ z : (R ⧸ maximalIdeal R) ⊗[R] K 0, (δ 0).baseChange (R ⧸ maximalIdeal R) z = 0 → z = 0)
  (hS : ∀ (i : ℕ) (z : (R ⧸ maximalIdeal R) ⊗[R] K (i + 1)),
    (δ (i + 1)).baseChange (R ⧸ maximalIdeal R) z = 0 →
      z ∈ LinearMap.range ((δ i).baseChange (R ⧸ maximalIdeal R))) :
  -- imply
  (∀ z : K 0, δ 0 z = 0 → z = 0) ∧
    ∀ (i : ℕ) (z : K (i + 1)), δ (i + 1) z = 0 → z ∈ LinearMap.range (δ i) := by
  -- proof
  classical
  apply helper_main K δ hdd _ _
  ·
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro z hz
    apply h0 z
    rw [LinearMap.baseChange_eq_ltensor]
    apply hz
  ·
    intro i z hz
    have hz' : (δ (i + 1)).baseChange (R ⧸ maximalIdeal R) z = 0 := by
      rw [LinearMap.baseChange_eq_ltensor]
      apply hz
    obtain ⟨y, hy⟩ := hS i z hz'
    rw [LinearMap.baseChange_eq_ltensor] at hy
    exact ⟨y, hy⟩


-- created on 2026-10-20
