import Mathlib
import Initialize.Tactic.Attr.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private noncomputable def N [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (r : R) : Module.End K M := T r - a r • (1 : Module.End K M)
private lemma N_apply [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (r : R) (x : M) : N T a r x = T r x - a r • x := by
  simp [N]
private lemma T_mul_comm [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (r s : R) : T r * T s = T s * T r := by
  rw [← map_mul, ← map_mul, mul_comm]
private lemma T_comm_apply [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (r s : R) (x : M) : T r (T s x) = T s (T r x) := by
  have h := congrArg (fun f : Module.End K M => f x) (T_mul_comm T r s)
  simpa using h
private lemma N_T_comm [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (r s : R) (x : M) : N T a r (T s x) = T s (N T a r x) := by
  rw [N_apply T a, N_apply T a, T_comm_apply T r s x, map_sub, map_smul]
private lemma N_pow_T_comm [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (r s : R) (k : ℕ) (x : M) : (N T a r ^ k) (T s x) = T s ((N T a r ^ k) x) := by
  induction k generalizing x
  · simp
  ·
    rename_i k ih
    rw [pow_succ, Module.End.mul_apply, Module.End.mul_apply, N_T_comm T a, ih]
private noncomputable def Stable [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (W : Submodule K M) : Prop := ∀ r : R, ∀ w ∈ W, T r w ∈ W
private lemma N_mem [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) {W : Submodule K M} (hW : Stable T W) (r : R) {w : M} (hw : w ∈ W) : N T a r w ∈ W := by
  rw [N_apply T a]
  exact W.sub_mem (hW r w hw) (W.smul_mem _ hw)
private lemma N_pow_mem [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) {W : Submodule K M} (hW : Stable T W) (r : R) (k : ℕ) {w : M} (hw : w ∈ W) : (N T a r ^ k) w ∈ W := by
  induction k generalizing w
  · simpa using hw
  ·
    rename_i k ih
    rw [pow_succ, Module.End.mul_apply]
    exact ih (N_mem T a hW r hw)
private lemma coe_restrict_pow_apply [Field K] [AddCommGroup M] [Module K M] (f : Module.End K M) {W : Submodule K M} (hf : ∀ w ∈ W, f w ∈ W) (k : ℕ) (x : W) : (((f.restrict hf) ^ k) x : M) = (f ^ k) (x : M) := by
  induction k generalizing x
  · simp
  ·
    rename_i k ih
    rw [pow_succ, Module.End.mul_apply, ih, pow_succ, Module.End.mul_apply, LinearMap.restrict_apply]
private lemma mu_N [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (μ : Module.Dual K M) (hco : ∀ r : R, LinearMap.comp μ (T r : M →ₗ[K] M) = a r • μ) (r : R) (x : M) : μ (N T a r x) = 0 := by
  have h := congrArg (fun f : Module.Dual K M => f x) (hco r)
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [N_apply T a, map_sub, map_smul, h, smul_eq_mul, sub_self]
private lemma mu_N_pow [Field K] [AddCommGroup M] [Module K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (μ : Module.Dual K M) (hco : ∀ r : R, LinearMap.comp μ (T r : M →ₗ[K] M) = a r • μ) (r : R) {k : ℕ} (hk : 0 < k) (x : M) : μ ((N T a r ^ k) x) = 0 := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  rw [pow_succ', Module.End.mul_apply, mu_N T a μ hco]
private lemma exists_of_nilpotent [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) : ∀ (n : ℕ) (W : Submodule K M), Module.finrank K W = n → W ≠ ⊥ → Stable T W → (∀ r : R, ∃ k : ℕ, ∀ w ∈ W, (N T a r ^ k) w = 0) → ∃ m ∈ W, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by
  intro n
  induction n using Nat.strong_induction_on
  ·
    rename_i n ih
    intro W hWn hWbot hW hnil
    classical
    if hall : ∀ r : R, ∀ w ∈ W, N T a r w = 0 then
      obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWbot
      refine ⟨w, hw, hw0, fun r => ?_⟩
      have h := hall r w hw
      rw [N_apply T a, sub_eq_zero] at h
      refine h
    else
      push Not at hall
      obtain ⟨r, w, hw, hNw⟩ := hall
      set W' : Submodule K M := W ⊓ LinearMap.ker (N T a r) with hW'
      have hW'le : W' ≤ W := inf_le_left
      have hW'st : Stable T W' := by
        intro s x hx
        refine ⟨hW s x hx.1, ?_⟩
        show T s x ∈ LinearMap.ker (N T a r)
        rw [LinearMap.mem_ker, N_T_comm T a, (LinearMap.mem_ker.mp hx.2), map_zero]
      obtain ⟨k, hk⟩ := hnil r
      have hP : ∃ j, (N T a r ^ j) w = 0 := ⟨k, hk w hw⟩
      set j := Nat.find hP with hj
      have hjspec : (N T a r ^ j) w = 0 := Nat.find_spec hP
      have hw0 : w ≠ 0 := fun h => hNw (by rw [h, map_zero])
      have hj0 : j ≠ 0 := by
        intro h0
        rw [h0, pow_zero, Module.End.one_apply] at hjspec
        exact hw0 hjspec
      obtain ⟨j', hj'⟩ := Nat.exists_eq_succ_of_ne_zero hj0
      have hv0 : (N T a r ^ j') w ≠ 0 := Nat.find_min hP (by rw [← hj, hj']; exact Nat.lt_succ_self j')
      have hvker : N T a r ((N T a r ^ j') w) = 0 := by
        rw [← Module.End.mul_apply, ← pow_succ', ← Nat.succ_eq_add_one, ← hj', hjspec]
      have hvW' : (N T a r ^ j') w ∈ W' := ⟨N_pow_mem T a hW r j' hw, LinearMap.mem_ker.mpr hvker⟩
      have hW'bot : W' ≠ ⊥ := fun h => hv0 ((Submodule.mem_bot K).mp (h ▸ hvW'))
      have hlt : W' < W := lt_of_le_of_ne hW'le fun h => hNw (LinearMap.mem_ker.mp (h.symm ▸ hw : w ∈ W').2)
      have hdim : Module.finrank K W' < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨m, hmW', hm0, hm⟩ := ih _ hdim W' rfl hW'bot hW'st fun s => by
        obtain ⟨k, hk⟩ := hnil s
        exact ⟨k, fun w hw => hk w (hW'le hw)⟩
      exact ⟨m, hW'le hmW', hm0, hm⟩
private lemma exists_of_mu_ne [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M] [CommRing R] (T : R →+* Module.End K M) (a : R →+* K) (μ : Module.Dual K M) (hco : ∀ r : R, LinearMap.comp μ (T r : M →ₗ[K] M) = a r • μ) : ∀ (n : ℕ) (W : Submodule K M), Module.finrank K W = n → Stable T W → (∃ w ∈ W, μ w ≠ 0) → ∃ m ∈ W, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by
  intro n
  induction n using Nat.strong_induction_on
  ·
    rename_i n ih
    intro W hWn hW hμW
    classical
    if hnil : ∀ r : R, ∃ k : ℕ, ∀ w ∈ W, (N T a r ^ k) w = 0 then
      obtain ⟨w, hw, hμw⟩ := hμW
      refine exists_of_nilpotent T a n W hWn ?_ hW hnil
      intro h
      obtain rfl := h
      rw [Submodule.mem_bot] at hw
      rw [hw, map_zero] at hμw
      exact hμw rfl
    else
      push Not at hnil
      obtain ⟨r, hr⟩ := hnil
      set f : Module.End K W := (N T a r).restrict (fun w hw => N_mem T a hW r hw) with hf
      obtain ⟨n₀, hn₀⟩ := Filter.eventually_atTop.mp (LinearMap.eventually_isCompl_ker_pow_range_pow f)
      set k := max n₀ 1 with hk
      have hkpos : 0 < k := lt_of_lt_of_le Nat.one_pos (le_max_right _ _)
      have hcompl : IsCompl (LinearMap.ker (f ^ k)) (LinearMap.range (f ^ k)) := hn₀ k (le_max_left _ _)
      set W₁ : Submodule K M := (LinearMap.ker (f ^ k)).map W.subtype with hW₁
      have hW₁le : W₁ ≤ W := by
        rintro _ ⟨x, -, rfl⟩
        exact x.2
      have hmemW₁ : ∀ {w : M} (hw : w ∈ W), w ∈ W₁ ↔ (N T a r ^ k) w = 0 := by
        intro w hw
        constructor
        ·
          rintro ⟨x, hx, hxw⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker] at hx
          have e := congrArg (fun y : W => (y : M)) hx
          rw [hf, coe_restrict_pow_apply, ZeroMemClass.coe_zero] at e
          rwa [show (x : M) = w from hxw] at e
        ·
          intro h0
          refine ⟨⟨w, hw⟩, ?_, rfl⟩
          rw [SetLike.mem_coe, LinearMap.mem_ker]
          apply Subtype.ext
          rw [hf, coe_restrict_pow_apply, ZeroMemClass.coe_zero]
          refine h0
      have hW₁st : Stable T W₁ := by
        intro s w hw
        have hwW : w ∈ W := hW₁le hw
        rw [hmemW₁ (hW s w hwW), N_pow_T_comm T a, (hmemW₁ hwW).mp hw, map_zero]
      have hμW₁ : ∃ w ∈ W₁, μ w ≠ 0 := by
        by_contra hcon
        push Not at hcon
        obtain ⟨w, hw, hμw⟩ := hμW
        apply hμw
        have htop : (⟨w, hw⟩ : W) ∈ LinearMap.ker (f ^ k) ⊔ LinearMap.range (f ^ k) := by
          rw [hcompl.sup_eq_top]
          refine Submodule.mem_top
        obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.mp htop
        obtain ⟨z, rfl⟩ := LinearMap.mem_range.mp hv
        have hwsum : w = (u : M) + (((f ^ k) z : W) : M) := by
          have := congrArg (fun y : W => (y : M)) huv
          simpa using this.symm
        have hu0 : μ (u : M) = 0 := hcon _ ⟨u, hu, rfl⟩
        rw [hwsum, map_add, hu0, hf, coe_restrict_pow_apply, mu_N_pow T a μ hco r hkpos, add_zero]
      have hW₁ne : W₁ ≠ W := by
        intro h
        obtain ⟨w, hw, hne⟩ := hr k
        exact hne ((hmemW₁ hw).mp (h.symm ▸ hw))
      have hlt : W₁ < W := lt_of_le_of_ne hW₁le hW₁ne
      have hdim : Module.finrank K W₁ < n := hWn ▸ Submodule.finrank_lt_finrank_of_lt hlt
      obtain ⟨m, hmW₁, hm0, hm⟩ := ih _ hdim W₁ rfl hW₁st hμW₁
      exact ⟨m, hW₁le hmW₁, hm0, hm⟩
/--
[Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Module_End_exists_ne_zero_forall_apply_eq_smul_of_dual_comp_eq_smul.lean)
-/
@[path]
private lemma main
  [Field K] [AddCommGroup M] [Module K M] [FiniteDimensional K M] [CommRing R]
  (T : R →+* Module.End K M)
  (a : R →+* K)
  (μ : Module.Dual K M)
  -- given
  (hμ : μ ≠ 0)
  (hco : ∀ r : R, LinearMap.comp μ (T r : M →ₗ[K] M) = a r • μ) :
  -- imply
  ∃ m : M, m ≠ 0 ∧ ∀ r : R, T r m = a r • m := by
  -- proof
  have hμtop : ∃ w ∈ (⊤ : Submodule K M), μ w ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hμ (LinearMap.ext fun x => hcon x Submodule.mem_top)
  obtain ⟨m, -, hm0, hm⟩ := exists_of_mu_ne T a μ hco _ ⊤ rfl (fun _ _ _ => Submodule.mem_top) hμtop
  exact ⟨m, hm0, hm⟩


-- created on 2026-10-20
