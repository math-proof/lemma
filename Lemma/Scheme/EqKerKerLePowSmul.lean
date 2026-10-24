import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

/--
[Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_existsUnique_compatible_lift_of_range_eq_ker_of_ker_le_pow_smul.lean)
-/
@[path]
private lemma main
  {R : Type u} [CommRing R] (I : Ideal R)
  (E : ℕ → Type u) [∀ k, AddCommGroup (E k)] [∀ k, Module R (E k)]
  (τ : ∀ k, E (k + 1) →ₗ[R] E k)
  (P : ℕ → Type u) [∀ k, AddCommGroup (P k)] [∀ k, Module R (P k)]
  (π : ∀ k, P (k + 1) →ₗ[R] P k)
  (C : ℕ → Type u) [∀ k, AddCommGroup (C k)] [∀ k, Module R (C k)]
  (θ : ∀ k, P k →ₗ[R] C k)
  (u : ∀ k, E k →ₗ[R] P k)
  (p : ∀ k, P k)
  -- given
  (hτs : ∀ k, Function.Surjective (τ k))
  (hτk : ∀ k, LinearMap.ker (τ k) = I ^ (k + 1) • (⊤ : Submodule R (E (k + 1))))
  (huc : ∀ k, LinearMap.comp (π k) (u (k + 1)) = LinearMap.comp (u k) (τ k))
  (hur : ∀ k, LinearMap.range (u k) = LinearMap.ker (θ k))
  (hui : ∃ c : ℕ, ∀ k : ℕ, LinearMap.ker (u (k + c)) ≤ I ^ (k + 1) • (⊤ : Submodule R (E (k + c))))
  (hp : ∀ k, π k (p (k + 1)) = p k)
  (hpθ : ∀ k, θ k (p k) = 0) :
  -- imply
  ∃! e : ∀ k, E k, (∀ k, τ k (e (k + 1)) = e k) ∧ ∀ k, u k (e k) = p k := by
  -- proof
  classical
  obtain ⟨c, hc⟩ := hui
  let T : (∀ k, E k) →ₗ[R] (∀ k, E k) := LinearMap.pi fun k => LinearMap.comp (τ k) (LinearMap.proj (k + 1))
  let S : (∀ k, P k) →ₗ[R] (∀ k, P k) := LinearMap.pi fun k => LinearMap.comp (π k) (LinearMap.proj (k + 1))
  let U : (∀ k, E k) →ₗ[R] (∀ k, P k) := LinearMap.pi fun k => LinearMap.comp (u k) (LinearMap.proj k)
  have hT : ∀ (x : ∀ k, E k) (k : ℕ), T x k = τ k (x (k + 1)) := fun x k => rfl
  have hS : ∀ (y : ∀ k, P k) (k : ℕ), S y k = π k (y (k + 1)) := fun y k => rfl
  have hU : ∀ (x : ∀ k, E k) (k : ℕ), U x k = u k (x k) := fun x k => rfl
  have hkill : ∀ (k : ℕ) (x : E k), x ∈ (I ^ (k + 1) • ⊤ : Submodule R (E k)) → x = 0 := by
    intro k x hx
    refine Submodule.smul_induction_on hx (fun a ha y _ => ?_) (fun x y hx hy => by rw [hx, hy, add_zero])
    obtain ⟨z, rfl⟩ := hτs k y
    rw [← map_smul]
    apply LinearMap.mem_ker.mp _
    rw [hτk k]
    apply Submodule.smul_mem_smul ha Submodule.mem_top
  have hinv : ∀ (j : ℕ) (x : ∀ k, E k), (∀ k, x k ∈ (I ^ (k + 1 + j - c) • ⊤ : Submodule R (E k))) → ∀ k, T x k ∈ (I ^ (k + 1 + (j + 1) - c) • ⊤ : Submodule R (E k)) := by
    intro j x hx k
    rw [hT]
    have h1 : x (k + 1) ∈ (I ^ (k + 1 + 1 + j - c) • ⊤ : Submodule R (E (k + 1))) := hx (k + 1)
    have h2 : Submodule.map (τ k) (I ^ (k + 1 + 1 + j - c) • ⊤ : Submodule R (E (k + 1))) ≤ (I ^ (k + 1 + (j + 1) - c) • ⊤ : Submodule R (E k)) := by
      rw [Submodule.map_smul'', show k + 1 + 1 + j - c = k + 1 + (j + 1) - c by omega]
      apply smul_mono_right _ le_top
    refine h2 ⟨_, h1, rfl⟩
  have hiter : ∀ (j : ℕ) (x : ∀ k, E k), (∀ k, x k ∈ (I ^ (k + 1 - c) • ⊤ : Submodule R (E k))) → ∀ k, (T ^ j) x k ∈ (I ^ (k + 1 + j - c) • ⊤ : Submodule R (E k)) := by
    intro j
    induction j
    ·
      intro x hx k
      rw [pow_zero, Module.End.one_apply, show k + 1 + 0 - c = k + 1 - c by omega]
      apply hx k
    ·
      rename_i j ih
      intro x hx k
      rw [pow_succ', Module.End.mul_apply]
      apply hinv j _ (ih x hx) k
  have hvanish : ∀ x : ∀ k, E k, U x = 0 → (T ^ c) x = 0 := by
    intro x hx
    have hx' : ∀ k, x k ∈ (I ^ (k + 1 - c) • ⊤ : Submodule R (E k)) := by
      intro k
      if hk : c ≤ k then
        obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' hk
        have hxk : x (m + c) ∈ LinearMap.ker (u (m + c)) := by
          have := congrFun hx (m + c)
          rw [hU] at this
          apply this
        have := hc m hxk
        rwa [show m + c + 1 - c = m + 1 by omega]
      else
        rw [show k + 1 - c = 0 by omega, pow_zero, Ideal.one_eq_top, Submodule.top_smul]
        trivial
    funext k
    have := hiter c x hx' k
    rw [show k + 1 + c - c = k + 1 by omega] at this
    apply hkill k _ this
  have hUT : ∀ x, U (T x) = S (U x) := by
    intro x
    funext k
    rw [hU, hT, hS, hU]
    apply (LinearMap.congr_fun (huc k) (x (k + 1))).symm
  have hUTi : ∀ (j : ℕ) (x : ∀ k, E k), U ((T ^ j) x) = (S ^ j) (U x) := by
    intro j
    induction j
    ·
      intro x
      rw [pow_zero, pow_zero, Module.End.one_apply, Module.End.one_apply]
    ·
      rename_i j ih
      intro x
      rw [pow_succ', pow_succ', Module.End.mul_apply, Module.End.mul_apply, hUT, ih]
  have hSp : S p = p := by
    funext k
    rw [hS]
    apply hp k
  have hSpi : ∀ j : ℕ, (S ^ j) p = p := by
    intro j
    induction j
    · rw [pow_zero, Module.End.one_apply]
    ·
      rename_i j ih
      rw [pow_succ', Module.End.mul_apply, ih, hSp]
  have hTpow : ∀ (j : ℕ) (x : ∀ k, E k), (T ^ j) (T x) = T ((T ^ j) x) := by
    intro j x
    rw [← Module.End.mul_apply, ← pow_succ, pow_succ', Module.End.mul_apply]
  have hex : ∀ k, ∃ y : E k, u k y = p k := by
    intro k
    have : p k ∈ LinearMap.range (u k) := by
      rw [hur k]
      apply hpθ k
    apply this
  choose e' he' using hex
  have hUe' : U e' = p := by
    funext k
    rw [hU]
    apply he' k
  have hTe : T ((T ^ c) e') = (T ^ c) e' := by
    have h1 : (T ^ c) (T e' - e') = 0 := hvanish _ (by rw [map_sub, hUT, hUe', hSp, sub_self])
    rw [map_sub, sub_eq_zero, hTpow] at h1
    apply h1
  have hUe : U ((T ^ c) e') = p := by rw [hUTi, hUe', hSpi]
  refine ⟨(T ^ c) e', ⟨fun k => ?_, fun k => ?_⟩, ?_⟩
  ·
    have := congrFun hTe k
    rw [hT] at this
    apply this
  ·
    have := congrFun hUe k
    rw [hU] at this
    apply this
  ·
    rintro e₂ ⟨h₂c, h₂u⟩
    have hTd : T (e₂ - (T ^ c) e') = e₂ - (T ^ c) e' := by
      rw [map_sub, hTe]
      congr 1
      funext k
      rw [hT]
      apply h₂c k
    have hUd : U (e₂ - (T ^ c) e') = 0 := by
      rw [map_sub, hUe, sub_eq_zero]
      funext k
      rw [hU]
      apply h₂u k
    have hfix : ∀ j : ℕ, (T ^ j) (e₂ - (T ^ c) e') = e₂ - (T ^ c) e' := by
      intro j
      induction j
      · rw [pow_zero, Module.End.one_apply]
      ·
        rename_i j ih
        rw [pow_succ', Module.End.mul_apply, ih, hTd]
    have := hvanish _ hUd
    rw [hfix] at this
    apply sub_eq_zero.mp this


-- created on 2026-10-20
