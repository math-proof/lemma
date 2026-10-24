import Mathlib
import sympy.Basic


private lemma mem_torsionBySet_ideal_iff
  {R M : Type*}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  (J : Ideal R) (x : M) :
  x ∈ Submodule.torsionBySet R M (J : Set R) ↔ ∀ a ∈ J, a • x = 0 := by
  rw [Submodule.mem_torsionBySet_iff, Subtype.forall]
  rfl

private lemma torsionBySet_pow_add_eq
  {R M : Type*}
  [CommRing R]
  [AddCommGroup M]
  [Module R M]
  (I : Ideal R) (N : ℕ)
  (hN : Submodule.torsionBySet R M (↑(I ^ (N + 1)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R))
  (k : ℕ) :
  Submodule.torsionBySet R M (↑(I ^ (N + k)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    apply le_antisymm
    ·
      intro x hx
      rw [← hN]
      rw [mem_torsionBySet_ideal_iff] at hx ⊢
      have hax : ∀ a ∈ I, a • x ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by
        intro a ha
        rw [← ih, mem_torsionBySet_ideal_iff]
        intro b hb
        rw [smul_smul]
        exact hx _ (by rw [← add_assoc, pow_succ]; exact Ideal.mul_mem_mul hb ha)
      intro c hc
      rw [pow_succ] at hc
      refine Submodule.mul_induction_on hc (fun b hb a ha => ?_) (fun y z hy hz => by rw [add_smul, hy, hz, add_zero])
      rw [mul_smul]
      exact (mem_torsionBySet_ideal_iff _ _).1 (hax a ha) b hb
    · exact Submodule.torsionBySet_le_torsionBySet_of_subset fun a ha =>
        Ideal.pow_le_pow_right (Nat.le_add_right N (k + 1)) ha
/--
[Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Submodule_exists_smul_eq_self_and_smul_mem_torsionBySet_of_torsionBySet_pow_succ_eq.lean)
-/
@[path]
private lemma main
  [CommRing R] [AddCommGroup M] [Module R M] [Finite M]
  {I : Ideal R}
  {N : ℕ}
-- given
  (hN : Submodule.torsionBySet R M (↑(I ^ (N + 1)) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R)) :
-- imply
  ∃ t : R, (∀ v ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R), t • v = v) ∧
      ∀ m : M, t • m ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by
-- proof
  classical
    have : IsArtinian R M := isArtinian_of_finite
    let f : ℕ →o (Submodule R M)ᵒᵈ :=
      ⟨fun k => OrderDual.toDual ((I ^ k) • (⊤ : Submodule R M)), fun k l hkl =>
        OrderDual.toDual_le_toDual.2 (Submodule.smul_mono_left (Ideal.pow_le_pow_right hkl))⟩
    obtain ⟨n₀, hn₀⟩ := IsArtinian.monotone_stabilizes f
    set n := max n₀ N + 1 with hn
    have hnN : N ≤ n := (le_max_right n₀ N).trans (Nat.le_succ _)
    have hn1 : 1 ≤ n := Nat.succ_le_succ (Nat.zero_le _)
    set M' : Submodule R M := (I ^ n) • ⊤ with hM'
    have hstab : (I ^ (n + 1)) • (⊤ : Submodule R M) = M' := by
      have h1 := hn₀ (n + 1) ((le_max_left n₀ N).trans (Nat.le_succ _) |>.trans (Nat.le_succ _))
      have h2 := hn₀ n ((le_max_left n₀ N).trans (Nat.le_succ _))
      refine (OrderDual.toDual.injective (h1.symm.trans h2) : _)
    have hfg : M'.FG := ⟨(M' : Set M).toFinite.toFinset, by rw [Set.Finite.coe_toFinset, Submodule.span_eq]⟩
    have hle : M' ≤ I • M' := by
      rw [hM', ← Submodule.mul_smul, ← pow_succ', hstab]
    obtain ⟨r, hrI, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul I M' hfg hle
    set u := r ^ n with hu
    have huM' : ∀ x ∈ M', u • x = 0 := by
      intro x hx
      obtain ⟨k, hk⟩ : ∃ k, n = k + 1 := ⟨n - 1, (Nat.sub_add_cancel hn1).symm⟩
      rw [hu, hk, pow_succ, mul_smul, hr x hx, smul_zero]
    have hcI : 1 - u ∈ I := by
      have h1 : Ideal.Quotient.mk I r = Ideal.Quotient.mk I 1 := (Ideal.Quotient.eq).2 hrI
      rw [map_one] at h1
      rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_one, hu, map_pow, h1, one_pow, sub_self]
    obtain ⟨q, hq⟩ : u ∣ 1 - (1 - u) ^ n := by
      have := one_sub_dvd_one_sub_pow (1 - u) n
      rwa [sub_sub_cancel] at this
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hnN
    have hNn : Submodule.torsionBySet R M (↑(I ^ n) : Set R) = Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by
      rw [hk]; exact torsionBySet_pow_add_eq I N hN k
    have key : ∀ y : M, u • y ∈ Submodule.torsionBySet R M (↑(I ^ N) : Set R) := by
      intro y
      rw [← hNn, mem_torsionBySet_ideal_iff]
      intro b hb
      rw [smul_comm]
      exact huM' _ (Submodule.smul_mem_smul hb Submodule.mem_top)
    refine ⟨1 - (1 - u) ^ n, fun v hv => ?_, fun m => ?_⟩
    ·
      have hv' : v ∈ Submodule.torsionBySet R M (↑(I ^ n) : Set R) := hNn ▸ hv
      rw [sub_smul, one_smul, sub_eq_self]
      exact (mem_torsionBySet_ideal_iff _ _).1 hv' _ (Ideal.pow_mem_pow hcI n)
    ·
      rw [hq, mul_smul]
      exact key (q • m)


-- created on 2026-10-23
