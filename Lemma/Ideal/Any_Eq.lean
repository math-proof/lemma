import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma smul_pow_injective [CommRing R] [AddCommGroup M] [Module R M] {N : Type*} [AddCommGroup N] [Module R N] (f : M →ₗ[R] N) (r : R) [IsLocalizedModule (Submonoid.powers r) f] (n : ℕ) {y y' : N} (h : r ^ n • y = r ^ n • y') : y = y' := by
  apply ((Module.End.isUnit_iff _).mp (IsLocalizedModule.map_units f (⟨r ^ n, n, rfl⟩ : Submonoid.powers r))).1 h
private lemma exists_common_numerators [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (g : ι → R) {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)] (x : ∀ i, N i) : ∃ (a : ℕ) (m : ι → M), ∀ i, g i ^ a • x i = f i (m i) := by
  classical
  have h1 : ∀ i, ∃ (n : ℕ) (m : M), g i ^ n • x i = f i m := by
    intro i
    obtain ⟨⟨m, ⟨_, n, rfl⟩⟩, hm⟩ := IsLocalizedModule.surj (Submonoid.powers (g i)) (f i) (x i)
    exact ⟨n, m, hm⟩
  choose n m hm using h1
  refine ⟨Finset.univ.sup n, fun i => g i ^ (Finset.univ.sup n - n i) • m i, fun i => ?_⟩
  have hle : n i ≤ Finset.univ.sup n := Finset.le_sup (Finset.mem_univ i)
  rw [map_smul, ← hm i, ← smul_assoc, smul_eq_mul, ← pow_add, Nat.sub_add_cancel hle]
private lemma exists_of_compatible [CommRing R] [AddCommGroup M] [Module R M] {ι : Type*} [Fintype ι] (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤) {N : ι → Type*} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)] (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)] {N₂ : ι → ι → Type*} [∀ i j, AddCommGroup (N₂ i j)] [∀ i j, Module R (N₂ i j)] (l : ∀ i j, N i →ₗ[R] N₂ i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g j)) (l i j)] (l' : ∀ i j, N j →ₗ[R] N₂ i j) (hll : ∀ i j, LinearMap.comp (l i j) (f i) = LinearMap.comp (l' i j) (f j)) (x : ∀ i, N i) (hx : ∀ i j, l i j (x i) = l' i j (x j)) : ∃ m : M, ∀ i, f i m = x i := by
  classical
  obtain ⟨a, m, hm⟩ := exists_common_numerators g f x
  have hkill : ∀ i j, ∃ b : ℕ, (g i * g j) ^ b • (g j ^ a • m i - g i ^ a • m j) = 0 := by
    intro i j
    have h0 : l i j (f i (g j ^ a • m i - g i ^ a • m j)) = 0 := by
      have e1 : l i j (f i (g i ^ a • m j)) = l' i j (f j (g i ^ a • m j)) := congrArg (fun φ : M →ₗ[R] N₂ i j => φ (g i ^ a • m j)) (hll i j)
      rw [map_sub, map_sub, e1, map_smul, map_smul, ← hm i, map_smul, map_smul, ← hm j, smul_smul, smul_smul, hx i j, mul_comm (g j ^ a) (g i ^ a), map_smul, sub_self]
    obtain ⟨⟨_, b₁, rfl⟩, hb₁⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g j)) (l i j)).mp (show l i j (f i (g j ^ a • m i - g i ^ a • m j)) = l i j 0 by rw [h0, map_zero])
    rw [smul_zero] at hb₁
    replace hb₁ : f i (g j ^ b₁ • (g j ^ a • m i - g i ^ a • m j)) = 0 := by
      rw [map_smul]
      apply hb₁
    obtain ⟨⟨_, b₂, rfl⟩, hb₂⟩ := (IsLocalizedModule.eq_iff_exists (Submonoid.powers (g i)) (f i)).mp (show f i (g j ^ b₁ • (g j ^ a • m i - g i ^ a • m j)) = f i 0 by rw [hb₁, map_zero])
    rw [smul_zero] at hb₂
    replace hb₂ : g i ^ b₂ • (g j ^ b₁ • (g j ^ a • m i - g i ^ a • m j)) = 0 := hb₂
    refine ⟨b₁ + b₂, ?_⟩
    rw [mul_pow, pow_add, pow_add, show g i ^ b₁ * g i ^ b₂ * (g j ^ b₁ * g j ^ b₂) = (g i ^ b₁ * g j ^ b₂) * (g i ^ b₂ * g j ^ b₁) by ring, mul_smul, mul_smul, mul_smul, hb₂, smul_zero, smul_zero]
  choose b hb using hkill
  let B : ℕ := Finset.univ.sup fun ij : ι × ι => b ij.1 ij.2
  have hB : ∀ i j, (g i * g j) ^ B • (g j ^ a • m i - g i ^ a • m j) = 0 := by
    intro i j
    have hle : b i j ≤ B := Finset.le_sup (f := fun ij : ι × ι => b ij.1 ij.2) (Finset.mem_univ (i, j))
    rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hb, smul_zero]
  let m' : ι → M := fun i => g i ^ B • m i
  have hsym : ∀ i j, g j ^ (a + B) • m' i = g i ^ (a + B) • m' j := by
    intro i j
    have h := hB i j
    rw [smul_sub, sub_eq_zero, smul_smul, smul_smul, mul_pow] at h
    simp [m']
    convert h using 2
    all_goals ring
  have hspan : Ideal.span (Set.range fun i => g i ^ (a + B)) = ⊤ := by
    have := Ideal.span_pow_eq_top (Set.range g) hg (a + B)
    rwa [← Set.range_comp] at this
  obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hspan ▸ Submodule.mem_top : (1 : R) ∈ _)
  refine ⟨∑ i, c i • m' i, fun j => ?_⟩
  have key : g j ^ (a + B) • ∑ i, c i • m' i = m' j := by
    rw [Finset.smul_sum]
    simp_rw [smul_comm (g j ^ (a + B)) (c _), hsym _ j, ← smul_assoc, ← Finset.sum_smul]
    simp_rw [smul_eq_mul]
    rw [hc, one_smul]
  apply smul_pow_injective (f j) (g j) (a + B)
  rw [← map_smul, key]
  simp [m']
  rw [map_smul, ← hm j, smul_smul, ← pow_add, add_comm]
/--
[IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_IsLocalizedModule_exists_forall_apply_eq_of_span_range_eq_top.lean)
-/
@[path]
private lemma main
  {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
  {ι : Type w} [Fintype ι]
  (g : ι → R) (hg : Ideal.span (Set.range g) = ⊤)
  {N : ι → Type v} [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M →ₗ[R] N i) [∀ i, IsLocalizedModule (Submonoid.powers (g i)) (f i)]
  {N₂ : ι → ι → Type v} [∀ i j, AddCommGroup (N₂ i j)] [∀ i j, Module R (N₂ i j)]
  (l : ∀ i j, N i →ₗ[R] N₂ i j) [∀ i j, IsLocalizedModule (Submonoid.powers (g j)) (l i j)]
  (l' : ∀ i j, N j →ₗ[R] N₂ i j)
  (hll : ∀ i j, LinearMap.comp (l i j) (f i) = LinearMap.comp (l' i j) (f j))
  (x : ∀ i, N i) (hx : ∀ i j, l i j (x i) = l' i j (x j)) :
  -- imply
  ∃ m : M, ∀ i, f i m = x i :=
  exists_of_compatible g hg f l l' hll x hx


-- created on 2026-10-20
