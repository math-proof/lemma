import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.SL2Representations
open Complex Module Classical in


/--
[GKModule.IsIsomorphicGK.trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma GKModule.IsIsomorphicGK.trans
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  [AddCommGroup U]
  [Module ℂ U]
  [LieRingModule 𝔤 U]
  [LieModule ℂ 𝔤 U]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {N : GKModule 𝔤 K 𝔨 Ad W}
  {P : GKModule 𝔤 K 𝔨 Ad U}
-- given
  (h₁ : M.IsIsomorphicGK N)
  (h₂ : N.IsIsomorphicGK P) :
-- imply
  M.IsIsomorphicGK P := by
-- proof
  obtain ⟨φ₁, hφ₁⟩ := h₁
  obtain ⟨φ₂, hφ₂⟩ := h₂
  exact ⟨{
    toLinearMap := φ₂.toLinearMap.comp φ₁.toLinearMap
    lie_comm := fun X v => by
      simp only [LinearMap.comp_apply, φ₁.lie_comm, φ₂.lie_comm]
    group_comm := fun k v => by
      simp only [LinearMap.comp_apply, φ₁.group_comm, φ₂.group_comm]
  }, hφ₂.comp hφ₁⟩

/--
[bddAbove_and_bddBelow_of_boundedBoth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma bddAbove_and_bddBelow_of_boundedBoth
  {𝔤 : Type*}
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  {K : Type*}
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  {V : Type*}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
-- given
  (hirr : M.IsIrreducibleGKModule)
  (hadm : M.IsAdmissible)
  (hbdd : sl2_gk_ktype_boundedness 𝔤 K 𝔨 Ad V M M_sl2 hirr hadm = .boundedBoth) :
-- imply
  BddAbove M_sl2.ktypeSet ∧ BddBelow M_sl2.ktypeSet := by
-- proof
  unfold sl2_gk_ktype_boundedness at hbdd
  split_ifs at hbdd with h1 h2
  · exact ⟨h1, h2⟩
  all_goals simp at hbdd

/--
[ktypeSet_uniform_parity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma ktypeSet_uniform_parity
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
-- given
  (hirr : M.IsIrreducibleGKModule) :
-- imply
  ∀ m ∈ M_sl2.ktypeSet, ∀ m' ∈ M_sl2.ktypeSet, (m : ℤ) % 2 = (m' : ℤ) % 2 := by
-- proof
  intro n hn m hm
  suffices h : Even n ↔ Even m by
    obtain ⟨k, hk⟩ | ⟨k, hk⟩ := Int.even_or_odd n
    · have hm_even := h.mp ⟨k, hk⟩
      obtain ⟨k', hk'⟩ := hm_even
      omega
    · have hm_odd : ¬ Even m := fun he => (Int.not_even_iff_odd.mpr ⟨k, hk⟩) (h.mpr he)
      have hn_odd : ¬ Even n := Int.not_even_iff_odd.mpr ⟨k, hk⟩
      rw [Int.not_even_iff_odd] at hm_odd hn_odd
      obtain ⟨k₁, hk₁⟩ := hn_odd
      obtain ⟨k₂, hk₂⟩ := hm_odd
      omega
  by_contra h_contra
  set S := ⨆ k : ℤ, M_sl2.weightSpace (n + 2 * k) with hS_def
  have hS_sub : M.IsSubmodule S := by
    constructor
    ·
      intro X w hw
      exact Submodule.iSup_induction (motive := fun w => ⁅X, w⁆ ∈ S)
        _ hw
        (fun k v hv => by
          obtain ⟨a, b, c, hX⟩ := SL2GKModule.sl2_generates M_sl2 X
          rw [hX]; simp only [add_lie, smul_lie]
          have hHv : ⁅M_sl2.H, v⁆ ∈ M_sl2.weightSpace (n + 2 * k) := by
            rw [SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2 (n + 2 * k) v hv]
            exact Submodule.smul_mem _ _ hv
          have hEv := SL2GKModule.E_shifts_weight M_sl2 (n + 2 * k) v hv
          have hFv := SL2GKModule.F_shifts_weight M_sl2 (n + 2 * k) v hv
          have ha : a • ⁅M_sl2.H, v⁆ ∈ S :=
            Submodule.mem_iSup_of_mem k (Submodule.smul_mem _ a hHv)
          have hb : b • ⁅M_sl2.E, v⁆ ∈ S := by
            apply Submodule.mem_iSup_of_mem (k + 1)
            have : n + 2 * (k + 1) = n + 2 * k + 2 := by ring
            rw [this]; exact Submodule.smul_mem _ b hEv
          have hc : c • ⁅M_sl2.F, v⁆ ∈ S := by
            apply Submodule.mem_iSup_of_mem (k - 1)
            have : n + 2 * (k - 1) = n + 2 * k - 2 := by ring
            rw [this]; exact Submodule.smul_mem _ c hFv
          exact Submodule.add_mem _ (Submodule.add_mem _ ha hb) hc)
        (by simp [lie_zero])
        (fun a b ha hb => by show ⁅X, a + b⁆ ∈ S; rw [lie_add]; exact Submodule.add_mem S ha hb)
    ·
      intro k w hw
      exact Submodule.iSup_induction (motive := fun w => M.σ k w ∈ S)
        _ hw
        (fun j v hv => by
          apply Submodule.mem_iSup_of_mem j
          rw [SL2GKModule.mem_weightSpace_iff] at hv ⊢
          have heq := M.equivariance k M_sl2.H v
          rw [M_sl2.K_centralizes k] at heq
          rw [hv] at heq; rw [map_smul] at heq
          exact heq.symm)
        (by simp [map_zero])
        (fun a b ha hb => by show M.σ k (a + b) ∈ S; rw [map_add]; exact Submodule.add_mem S ha hb)
  have hS_ne_bot : S ≠ ⊥ := by
    intro hbot; apply hn
    rw [eq_bot_iff]
    calc M_sl2.weightSpace n
      = M_sl2.weightSpace (n + 2 * 0) := by ring_nf
      _ ≤ S := le_iSup (fun k : ℤ => M_sl2.weightSpace (n + 2 * k)) 0
      _ = ⊥ := hbot
  have hS_top : S = ⊤ := by
    obtain hbot | htop := hirr S hS_sub
    · exact absurd hbot hS_ne_bot
    · exact htop
  have hne : ∀ k : ℤ, (m : ℂ) ≠ (↑(n + 2 * k) : ℂ) := by
    intro k heq
    have hmk : m = n + 2 * k := by exact_mod_cast heq
    exact h_contra (by subst hmk; simp [Int.even_add])
  have hdisjoint : Disjoint (M_sl2.weightSpace m) S := by
    have hind := Module.End.independent_genEigenspace M_sl2.hEnd (1 : ℕ∞)
    have hdisjoint_ind := hind (↑m)
    have hle : S ≤ ⨆ μ, ⨆ (_ : μ ≠ (↑m : ℂ)), M_sl2.hEnd.eigenspace μ := by
      apply iSup_le; intro k
      have hne_k : (↑(n + 2 * k) : ℂ) ≠ ↑m := (hne k).symm
      exact le_trans
        (le_iSup (fun _ : (↑(n + 2 * k) : ℂ) ≠ ↑m => M_sl2.hEnd.eigenspace ↑(n + 2 * k)) hne_k)
        (le_iSup (fun μ : ℂ => ⨆ (_ : μ ≠ ↑m), M_sl2.hEnd.eigenspace μ) ↑(n + 2 * k))
    exact Disjoint.mono_right hle hdisjoint_ind
  have hm_bot : M_sl2.weightSpace m = ⊥ := by
    rw [disjoint_iff] at hdisjoint
    calc M_sl2.weightSpace m
      = M_sl2.weightSpace m ⊓ ⊤ := (inf_top_eq _).symm
      _ = M_sl2.weightSpace m ⊓ S := by rw [hS_top]
      _ = ⊥ := hdisjoint
  exact hm hm_bot

/--
[sl2_EF_recurrence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma sl2_EF_recurrence
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
  {n₀ : ℤ}
  {v : V}
  {k : ℕ}
-- given
  (hv : v ∈ M_sl2.weightSpace n₀)
  (hEv : ⁅M_sl2.E, v⁆ = 0) :
-- imply
  ⁅M_sl2.E, SL2GKModule.iterLie M_sl2.F v (k + 1)⁆ = ((↑(k + 1) : ℂ) * (↑n₀ - ↑k)) • SL2GKModule.iterLie M_sl2.F v k := by
-- proof
  induction k with
  | zero =>
    simp only [SL2GKModule.iterLie_succ, SL2GKModule.iterLie_zero]
    rw [leibniz_lie M_sl2.E M_sl2.F v]
    rw [M_sl2.bracket_EF]
    rw [hEv, lie_zero, add_zero]
    rw [SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2 n₀ v hv]
    congr 1
    push_cast
    ring
  | succ k ih =>
    simp only [SL2GKModule.iterLie_succ] at ih ⊢
    set w := SL2GKModule.iterLie M_sl2.F v k with hw_def
    rw [leibniz_lie M_sl2.E M_sl2.F (⁅M_sl2.F, w⁆)]
    rw [M_sl2.bracket_EF]
    have hw_ws : w ∈ M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ)) :=
      SL2GKModule.iterLie_F_weight_shift M_sl2 n₀ v hv k
    have hFw_ws : ⁅M_sl2.F, w⁆ ∈ M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ) - 2) :=
      SL2GKModule.F_shifts_weight M_sl2 (n₀ - 2 * (↑k : ℤ)) w hw_ws
    have hH_Fw := SL2GKModule.H_acts_as_scalar_on_weight_space M_sl2
      (n₀ - 2 * (↑k : ℤ) - 2) (⁅M_sl2.F, w⁆) hFw_ws
    rw [hH_Fw]
    rw [ih, lie_smul]
    rw [← add_smul]
    congr 1
    push_cast
    ring

/--
[ktypeSet_max_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma ktypeSet_max_nonneg
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {M_sl2 : SL2GKModule 𝔤 K 𝔨 Ad V}
  {S : Finset ℤ}
-- given
  (hirr : M.IsIrreducibleGKModule)
  (hS : (↑S : Set ℤ) = M_sl2.ktypeSet)
  (hne : S.Nonempty) :
-- imply
  0 ≤ S.max' hne := by
-- proof
  set n₀ := S.max' hne with hn₀_def
  have hn₀_mem : n₀ ∈ S := Finset.max'_mem S hne
  have hn₀_ktype : n₀ ∈ M_sl2.ktypeSet := by rwa [← hS, Finset.mem_coe]
  have hws_ne : M_sl2.weightSpace n₀ ≠ ⊥ := hn₀_ktype
  rw [Submodule.ne_bot_iff] at hws_ne
  obtain ⟨v, hv_mem, hv_ne⟩ := hws_ne
  have hEv_zero : ⁅M_sl2.E, v⁆ = 0 := by
    have hEv_ws := SL2GKModule.E_shifts_weight M_sl2 n₀ v hv_mem
    have hn₀_plus_2_notin : n₀ + 2 ∉ S := by
      intro hmem
      have := Finset.le_max' S (n₀ + 2) hmem
      omega
    have hws_bot : M_sl2.weightSpace (n₀ + 2) = ⊥ := by
      by_contra hne_bot
      have : n₀ + 2 ∈ M_sl2.ktypeSet := hne_bot
      rw [← hS] at this
      exact hn₀_plus_2_notin (Finset.mem_coe.mp this)
    rw [Submodule.eq_bot_iff] at hws_bot
    exact hws_bot _ hEv_ws
  have hiter_ws : ∀ k : ℕ, SL2GKModule.iterLie M_sl2.F v k ∈
    M_sl2.weightSpace (n₀ - 2 * (↑k : ℤ)) :=
    SL2GKModule.iterLie_F_weight_shift M_sl2 n₀ v hv_mem
  have hfin_nonzero : Set.Finite {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0} := by
    let f : ℕ → ℤ := fun k => n₀ - 2 * (↑k : ℤ)
    have hf_inj : Function.Injective f := fun k₁ k₂ h => by
      simp only [f] at h; omega
    apply Set.Finite.subset (S.finite_toSet.preimage hf_inj.injOn)
    intro k hk
    simp only [Set.mem_setOf_eq] at hk
    show f k ∈ (↑S : Set ℤ)
    rw [hS]
    exact (Submodule.ne_bot_iff _).mpr ⟨_, hiter_ws k, hk⟩
  have h0_mem : (0 : ℕ) ∈ {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0} := by
    simp [SL2GKModule.iterLie_zero, hv_ne]
  have hfin_ne : {k : ℕ | SL2GKModule.iterLie M_sl2.F v k ≠ 0}.Nonempty :=
    ⟨0, h0_mem⟩
  let T := hfin_nonzero.toFinset
  have hT_ne : T.Nonempty := by
    rwa [Set.Finite.toFinset_nonempty]
  set N := T.max' hT_ne with hN_def
  have hN_mem : SL2GKModule.iterLie M_sl2.F v N ≠ 0 := by
    have := Finset.max'_mem T hT_ne
    rwa [Set.Finite.mem_toFinset] at this
  have hN_succ_zero : SL2GKModule.iterLie M_sl2.F v (N + 1) = 0 := by
    by_contra hne
    have hN1_mem : N + 1 ∈ T := by
      rwa [Set.Finite.mem_toFinset]
    have := Finset.le_max' T (N + 1) hN1_mem
    omega
  have hrec := sl2_EF_recurrence M_sl2 n₀ v hv_mem hEv_zero N
  rw [hN_succ_zero, lie_zero] at hrec
  rw [eq_comm] at hrec
  have hscalar_zero : (↑(N + 1) : ℂ) * (↑n₀ - ↑(N : ℤ)) = 0 := by
    by_contra hne
    exact hN_mem (smul_eq_zero.mp hrec |>.resolve_left hne)
  have hN1_ne : (↑(N + 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.succ_ne_zero N
  have hn₀_eq : (↑n₀ : ℂ) = (↑(N : ℤ) : ℂ) := by
    have := mul_eq_zero.mp hscalar_zero
    cases this with
    | inl h => exact absurd h hN1_ne
    | inr h => exact sub_eq_zero.mp h
  have hn₀_eq_int : n₀ = ↑N := by exact_mod_cast hn₀_eq
  omega

/--
[sl2_finiteDim_bracket_HE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma sl2_finiteDim_bracket_HE
  {n : ℕ} :
-- imply
  sl2_finiteDim_ρH n ∘ₗ sl2_finiteDim_ρE n - sl2_finiteDim_ρE n ∘ₗ sl2_finiteDim_ρH n = (2 : ℂ) • sl2_finiteDim_ρE n := by
-- proof
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · push_cast; ring
  · simp

/--
[sl2_finiteDim_bracket_HF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma sl2_finiteDim_bracket_HF
  {n : ℕ} :
-- imply
  sl2_finiteDim_ρH n ∘ₗ sl2_finiteDim_ρF n - sl2_finiteDim_ρF n ∘ₗ sl2_finiteDim_ρH n = -(2 : ℂ) • sl2_finiteDim_ρF n := by
-- proof
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs with h
  · simp only [Nat.cast_sub (show 1 ≤ i from h)]; ring
  · simp

/--
[sl2_finiteDim_bracket_EF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma sl2_finiteDim_bracket_EF
  {n : ℕ} :
-- imply
  sl2_finiteDim_ρE n ∘ₗ sl2_finiteDim_ρF n - sl2_finiteDim_ρF n ∘ₗ sl2_finiteDim_ρE n = sl2_finiteDim_ρH n := by
-- proof
  ext v ⟨i, hi⟩
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    sl2_finiteDim_ρH, sl2_finiteDim_ρE, sl2_finiteDim_ρF,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  simp only [dif_pos (Nat.succ_pos i)]
  have hfin1 : ∀ (h : i + 1 - 1 < n + 1), (⟨i + 1 - 1, h⟩ : Fin (n+1)) = ⟨i, hi⟩ :=
    fun _ => Fin.ext (Nat.succ_sub_one i)
  simp only [hfin1]
  by_cases h2 : 0 < i
  · simp only [dif_pos h2]
    have h3 : i - 1 + 1 ≤ n := by omega
    simp only [dif_pos h3]
    have hfin2 : ∀ (h : i - 1 + 1 < n + 1), (⟨i - 1 + 1, h⟩ : Fin (n+1)) = ⟨i, hi⟩ :=
      fun _ => Fin.ext (Nat.succ_pred_eq_of_pos h2)
    simp only [hfin2, Nat.cast_sub h2]
    by_cases h1 : i + 1 ≤ n
    · simp only [dif_pos h1]; push_cast; ring
    · simp only [dif_neg h1]; push_cast
      have h_in : (i : ℂ) = (n : ℂ) := by exact_mod_cast (show i = n from by omega)
      rw [h_in]; ring
  · simp only [dif_neg h2]
    have h_i0 : i = 0 := by omega
    subst h_i0
    by_cases h1 : 0 + 1 ≤ n
    · simp only [dif_pos h1]; push_cast; ring
    · simp only [dif_neg h1]; push_cast
      have h_n0 : (n : ℂ) = 0 := by exact_mod_cast (show n = 0 from by omega)
      rw [h_n0]; ring

/--
[principalSeries_bracket_HE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_bracket_HE
  {ν : ℂ}
  {ε : ZMod 2} :
-- imply
  principalSeries_ρH ν ε ∘ₗ principalSeries_ρE ν ε - principalSeries_ρE ν ε ∘ₗ principalSeries_ρH ν ε = (2 : ℂ) • principalSeries_ρE ν ε := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    principalSeries_ρH, principalSeries_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/--
[principalSeries_bracket_HF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_bracket_HF
  {ν : ℂ}
  {ε : ZMod 2} :
-- imply
  principalSeries_ρH ν ε ∘ₗ principalSeries_ρF ν ε - principalSeries_ρF ν ε ∘ₗ principalSeries_ρH ν ε = -(2 : ℂ) • principalSeries_ρF ν ε := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    principalSeries_ρH, principalSeries_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/--
[principalSeries_bracket_EF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_bracket_EF
  {ν : ℂ}
  {ε : ZMod 2} :
-- imply
  principalSeries_ρE ν ε ∘ₗ principalSeries_ρF ν ε - principalSeries_ρF ν ε ∘ₗ principalSeries_ρE ν ε = principalSeries_ρH ν ε := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, LinearMap.sub_apply,
    principalSeries_ρH, principalSeries_ρE, principalSeries_ρF,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
  push_cast
  ring

/--
[discreteSeriesPlus_bracket_HE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesPlus_bracket_HE
  {n : ℕ} :
-- imply
  discreteSeriesPlus_ρH n ∘ₗ discreteSeriesPlus_ρE n - discreteSeriesPlus_ρE n ∘ₗ discreteSeriesPlus_ρH n = (2 : ℂ) • discreteSeriesPlus_ρE n := by
-- proof
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/--
[discreteSeriesPlus_bracket_HF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesPlus_bracket_HF
  {n : ℕ} :
-- imply
  discreteSeriesPlus_ρH n ∘ₗ discreteSeriesPlus_ρF n - discreteSeriesPlus_ρF n ∘ₗ discreteSeriesPlus_ρH n = -(2 : ℂ) • discreteSeriesPlus_ρF n := by
-- proof
  ext f k
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    discreteSeriesPlus_ρH, discreteSeriesPlus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/--
[discreteSeriesPlus_bracket_EF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesPlus_bracket_EF
  {n : ℕ} :
-- imply
  discreteSeriesPlus_ρE n ∘ₗ discreteSeriesPlus_ρF n - discreteSeriesPlus_ρF n ∘ₗ discreteSeriesPlus_ρE n = discreteSeriesPlus_ρH n := by
-- proof
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, discreteSeriesPlus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesPlus_ρH, discreteSeriesPlus_ρE, discreteSeriesPlus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring

/--
[discreteSeriesMinus_bracket_HE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesMinus_bracket_HE
  {n : ℕ} :
-- imply
  discreteSeriesMinus_ρH n ∘ₗ discreteSeriesMinus_ρE n - discreteSeriesMinus_ρE n ∘ₗ discreteSeriesMinus_ρH n = (2 : ℂ) • discreteSeriesMinus_ρE n := by
-- proof
  ext f k
  simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
    discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, LinearMap.coe_mk, AddHom.coe_mk,
    Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

/--
[discreteSeriesMinus_bracket_HF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesMinus_bracket_HF
  {n : ℕ} :
-- imply
  discreteSeriesMinus_ρH n ∘ₗ discreteSeriesMinus_ρF n - discreteSeriesMinus_ρF n ∘ₗ discreteSeriesMinus_ρH n = -(2 : ℂ) • discreteSeriesMinus_ρF n := by
-- proof
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.smul_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρF, LinearMap.coe_mk, AddHom.coe_mk,
      Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/--
[discreteSeriesMinus_bracket_EF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma discreteSeriesMinus_bracket_EF
  {n : ℕ} :
-- imply
  discreteSeriesMinus_ρE n ∘ₗ discreteSeriesMinus_ρF n - discreteSeriesMinus_ρF n ∘ₗ discreteSeriesMinus_ρE n = discreteSeriesMinus_ρH n := by
-- proof
  ext f k
  match k with
  | 0 =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, discreteSeriesMinus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring
  | Nat.succ j =>
    simp only [LinearMap.comp_apply, LinearMap.sub_apply,
      discreteSeriesMinus_ρH, discreteSeriesMinus_ρE, discreteSeriesMinus_ρF,
      LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply]
    push_cast
    ring

/--
[principalSeries_neg_map_intertwine_H](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_neg_map_intertwine_H
  {c : ℤ → ℂ}
  {ν : ℂ}
  {ε : ZMod 2} :
-- imply
  principalSeries_neg_map c ∘ₗ principalSeries_ρH ν ε = principalSeries_ρH (-ν) ε ∘ₗ principalSeries_neg_map c := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρH,
    LinearMap.coe_mk, AddHom.coe_mk]
  ring

/--
[principalSeries_neg_map_intertwine_E](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_neg_map_intertwine_E
  {c : ℤ → ℂ}
  {ν : ℂ}
  {ε : ZMod 2}
-- given
  (hc : PrincipalSeries_neg_recurrence c ν) :
-- imply
  principalSeries_neg_map c ∘ₗ principalSeries_ρE ν ε = principalSeries_ρE (-ν) ε ∘ₗ principalSeries_neg_map c := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρE,
    LinearMap.coe_mk, AddHom.coe_mk]
  linear_combination (1/2 * f (m - 2)) * hc m

/--
[principalSeries_neg_map_intertwine_F](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma principalSeries_neg_map_intertwine_F
  {c : ℤ → ℂ}
  {ν : ℂ}
  {ε : ZMod 2}
-- given
  (hc : PrincipalSeries_neg_recurrence c ν) :
-- imply
  principalSeries_neg_map c ∘ₗ principalSeries_ρF ν ε = principalSeries_ρF (-ν) ε ∘ₗ principalSeries_neg_map c := by
-- proof
  ext f m
  simp only [LinearMap.comp_apply, principalSeries_neg_map, principalSeries_ρF,
    LinearMap.coe_mk, AddHom.coe_mk]
  have hc_shift := hc (m + 2)
  simp only [show (m + 2 : ℤ) - 2 = m from by omega] at hc_shift
  have cast_eq : (↑(m + 2) : ℂ) = (↑m : ℂ) + 2 := by push_cast; ring
  rw [cast_eq] at hc_shift
  linear_combination 1/2 * f (m + 2) * hc_shift

/--
[casimirEnd_equivariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma casimirEnd_equivariant
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {φ : V →ₗ[ℂ] W}
  {H E F : 𝔤}
  {v : V}
-- given
  (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆) :
-- imply
  φ (casimirEnd H E F v) = casimirEnd H E F (φ v) := by
-- proof
  unfold casimirEnd
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [map_add, map_add, map_nsmul, map_nsmul]
  have lie2 : ∀ (X Y : 𝔤) (u : V),
    φ ((LieModule.toEnd ℂ 𝔤 V X) ((LieModule.toEnd ℂ 𝔤 V Y) u)) =
    (LieModule.toEnd ℂ 𝔤 W X) ((LieModule.toEnd ℂ 𝔤 W Y) (φ u)) := by
    intros X Y u
    change φ ⁅X, ⁅Y, u⁆⁆ = ⁅X, ⁅Y, φ u⁆⁆
    rw [hcomm X, hcomm Y]
  congr 1
  · congr 1
    · exact lie2 H H v
    · congr 1; exact lie2 E F v
  · congr 1; exact lie2 F E v

/--
[casimirEigenvalues_iso_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma casimirEigenvalues_iso_invariant
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {φ : V →ₗ[ℂ] W}
  {H E F : 𝔤}
-- given
  (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆)
  (hbij : Function.Bijective φ) :
-- imply
  @casimirEigenvalues 𝔤 _ _ V _ _ _ _ H E F = @casimirEigenvalues 𝔤 _ _ W _ _ _ _ H E F := by
-- proof
  ext c
  simp only [casimirEigenvalues, Set.mem_setOf_eq]
  constructor
  · intro hV
    rw [Submodule.ne_bot_iff] at hV ⊢
    obtain ⟨v, hv, hv0⟩ := hV
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨φ v, ?_, fun h => hv0 (hbij.injective (by rw [h, map_zero]))⟩
    rw [Module.End.mem_eigenspace_iff]
    calc casimirEnd H E F (φ v)
      = φ (casimirEnd H E F v) := (casimirEnd_equivariant φ hcomm H E F v).symm
      _ = φ (c • v) := by rw [hv]
      _ = c • φ v := map_smul φ _ _
  · intro hW
    rw [Submodule.ne_bot_iff] at hW ⊢
    obtain ⟨w, hw, hw0⟩ := hW
    rw [Module.End.mem_eigenspace_iff] at hw
    obtain ⟨v, rfl⟩ := hbij.surjective w
    refine ⟨v, ?_, fun h => hw0 (by rw [h, map_zero])⟩
    rw [Module.End.mem_eigenspace_iff]
    apply hbij.injective
    calc φ (casimirEnd H E F v)
      = casimirEnd H E F (φ v) := casimirEnd_equivariant φ hcomm H E F v
      _ = c • φ v := hw
      _ = φ (c • v) := (map_smul φ _ _).symm

/--
[kTypesWrtH_iso_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma kTypesWrtH_iso_invariant
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {φ : V →ₗ[ℂ] W}
  {H : 𝔤}
-- given
  (hcomm : ∀ (X : 𝔤) (v : V), φ ⁅X, v⁆ = ⁅X, φ v⁆)
  (hbij : Function.Bijective φ) :
-- imply
  @kTypesWrtH 𝔤 _ _ V _ _ _ _ H = @kTypesWrtH 𝔤 _ _ W _ _ _ _ H := by
-- proof
  ext n
  simp only [kTypesWrtH, Set.mem_setOf_eq]
  have hH : ∀ v, φ ((LieModule.toEnd ℂ 𝔤 V) H v) = (LieModule.toEnd ℂ 𝔤 W) H (φ v) :=
    fun v => hcomm H v
  constructor
  ·
    intro hV
    rw [Submodule.ne_bot_iff] at hV ⊢
    obtain ⟨v, hv, hv0⟩ := hV
    rw [Module.End.mem_eigenspace_iff] at hv
    refine ⟨φ v, ?_, fun h => hv0 (hbij.injective (by rw [h, map_zero]))⟩
    rw [Module.End.mem_eigenspace_iff]
    calc (LieModule.toEnd ℂ 𝔤 W) H (φ v)
      = φ ((LieModule.toEnd ℂ 𝔤 V) H v) := (hH v).symm
      _ = φ ((n : ℂ) • v) := by rw [hv]
      _ = (n : ℂ) • φ v := map_smul φ _ _
  ·
    intro hW
    rw [Submodule.ne_bot_iff] at hW ⊢
    obtain ⟨w, hw, hw0⟩ := hW
    rw [Module.End.mem_eigenspace_iff] at hw
    obtain ⟨v, rfl⟩ := hbij.surjective w
    refine ⟨v, ?_, fun h => hw0 (by rw [h, map_zero])⟩
    rw [Module.End.mem_eigenspace_iff]
    apply hbij.injective
    calc φ ((LieModule.toEnd ℂ 𝔤 V) H v)
      = (LieModule.toEnd ℂ 𝔤 W) H (φ v) := hH v
      _ = (n : ℂ) • φ v := hw
      _ = φ ((n : ℂ) • v) := (map_smul φ _ _).symm

/--
[label_eq_of_invariants_match](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma label_eq_of_invariants_match
  {μ ν : SL2IrredGKModule}
-- given
  (hcas : μ.casimirEigenvalue = ν.casimirEigenvalue)
  (hkt : μ.kTypes = ν.kTypes) :
-- imply
  μ = ν ∨ (∃ s ε, μ = .principalSeries s ε ∧ ν = .principalSeries (-s) ε) := by
-- proof
  cases μ with
  | finiteDim n =>
    cases ν with
    | finiteDim m =>
      left; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x : ℤ | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn
      have hm : (m : ℤ) ∈ ({x : ℤ | x % 2 = (m : ℤ) % 2 ∧ x.natAbs ≤ m} : Set ℤ) := by simp
      rw [← hkt] at hm; simp at hm
      congr; omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn
      have hpar : ((↑n + 2 : ℤ) : ZMod 2) = ε := by push_cast; rw [show (2 : ZMod 2) = 0 from by decide, add_zero, hn]
      have h3 : (↑n + 2 : ℤ) ∈ ({m | (m : ZMod 2) = ε} : Set ℤ) := hpar
      rw [← hkt] at h3; simp at h3; omega
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp only [Set.mem_setOf_eq] at hn
      have hbig : (↑n + 2 : ℤ) ∈ ({x | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn : (n : ℤ) ∈ ({x | x % 2 = (n : ℤ) % 2 ∧ x.natAbs ≤ n} : Set ℤ) := by simp
      rw [hkt] at hn; simp at hn; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (↑n + 2 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (-(↑n + 2) : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [← hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑n + 2 : ℤ).natAbs : ℤ) = ↑n + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑n + 2 : ℤ) ≤ ↑n := by
        calc (↑n + 2 : ℤ) = ↑(↑n + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑n := by exact_mod_cast hbig.2
      omega
  | principalSeries ν₁ ε₁ =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hm : (m : ℤ) ∈ ({x | x % 2 = (m : ℤ) % 2 ∧ x.natAbs ≤ m} : Set ℤ) := by simp
      rw [← hkt] at hm; simp at hm
      have hpar : ((↑m + 2 : ℤ) : ZMod 2) = ε₁ := by push_cast; rw [show (2 : ZMod 2) = 0 from by decide, add_zero, hm]
      have h3 : (↑m + 2 : ℤ) ∈ ({x | (x : ZMod 2) = ε₁} : Set ℤ) := hpar
      rw [hkt] at h3; simp at h3; omega
    | principalSeries ν₂ ε₂ =>
      simp only [kTypes] at hkt
      have hε : ε₁ = ε₂ := by
        have h0 : ((0 : ℤ) : ZMod 2) = ε₁ ↔ ((0 : ℤ) : ZMod 2) = ε₂ := by
          constructor
          · intro hx; have := (hkt ▸ hx : (0 : ℤ) ∈ ({m | (m : ZMod 2) = ε₂} : Set ℤ)); exact this
          · intro hx; have := (hkt ▸ hx : (0 : ℤ) ∈ ({m | (m : ZMod 2) = ε₁} : Set ℤ)); exact this
        simp only [Int.cast_zero] at h0
        fin_cases ε₁ <;> fin_cases ε₂ <;> simp_all (config := { decide := true })
      subst hε
      simp only [casimirEigenvalue] at hcas
      have hν : ν₁ ^ 2 = ν₂ ^ 2 := sub_right_injective hcas
      have h2 : ((ν₁ - ν₂) * (ν₁ + ν₂) : ℂ) = 0 := by
        have := sub_eq_zero.mpr hν; ring_nf; exact this
      obtain h3 | h3 := mul_eq_zero.mp h2
      · left; congr; exact sub_eq_zero.mp h3
      · right; exact ⟨ν₁, ε₁, rfl, by congr 1; exact eq_neg_of_add_eq_zero_right h3⟩
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-(m : ℤ)) ∉ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have hm_in : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm_in; simp at hm_in; exact hm_in
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (m : ℤ) ∉ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [← hkt]
      have hm_in : (-(m : ℤ)) ∈ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [← hkt] at hm_in; simp at hm_in
      simp [Set.mem_setOf_eq]; exact hm_in
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∉ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have h2 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h2; simp at h2; exact h2
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∉ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [← hkt]; simp [Set.mem_setOf_eq]
      have h2 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h2; simp at h2; exact h2
  | discreteSeriesPlus n hn =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp only [Set.mem_setOf_eq] at hn2
      have hbig : (↑m + 2 : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-(n : ℤ)) ∉ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; exact hn2
    | discreteSeriesPlus m hm =>
      left; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2
      have hm2 : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm2; simp at hm2
      have heq : n = m := by omega
      subst heq; rfl
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (n : ℤ) ∈ ({x : ℤ | x ≥ (n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by simp
      rw [hkt] at hn2; simp at hn2; omega
  | discreteSeriesMinus n hn =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> simp <;> omega
      rw [hkt] at hn2; simp only [Set.mem_setOf_eq] at hn2
      have hbig : (-(↑m + 2) : ℤ) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (n : ℤ) ∉ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        simp; omega
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [hkt] at hn2; simp at hn2; exact hn2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have hm2 : (m : ℤ) ∈ ({x : ℤ | x ≥ (m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by simp
      rw [← hkt] at hm2; simp at hm2; omega
    | discreteSeriesMinus m hm =>
      left; simp only [kTypes] at hkt
      have hn2 : (-(n : ℤ)) ∈ ({x : ℤ | x ≤ -(n : ℤ) ∧ x % 2 = (n : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [hkt] at hn2; simp at hn2
      have hm2 : (-(m : ℤ)) ∈ ({x : ℤ | x ≤ -(m : ℤ) ∧ x % 2 = (m : ℤ) % 2} : Set ℤ) := by
        constructor <;> simp <;> omega
      rw [← hkt] at hm2; simp at hm2
      have heq : n = m := by omega
      subst heq; rfl
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1; omega
  | limitDiscretePlus =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (↑m + 2 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∉ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have h2 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h2; simp at h2; exact h2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | limitDiscretePlus => left; rfl
    | limitDiscreteMinus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1
  | limitDiscreteMinus =>
    cases ν with
    | finiteDim m =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp only [Set.mem_setOf_eq] at h1
      have hbig : (-(↑m + 2) : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by
        simp only [Set.mem_setOf_eq]; constructor <;> omega
      rw [hkt] at hbig; simp only [Set.mem_setOf_eq] at hbig
      simp only [Int.natAbs_neg] at hbig
      have h4 : (↑(↑m + 2 : ℤ).natAbs : ℤ) = ↑m + 2 := Int.natAbs_of_nonneg (by omega)
      have : (↑m + 2 : ℤ) ≤ ↑m := by
        calc (↑m + 2 : ℤ) = ↑(↑m + 2 : ℤ).natAbs := h4.symm
        _ ≤ ↑m := by exact_mod_cast hbig.2
      omega
    | principalSeries ν' ε =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∉ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      apply h1; rw [hkt]; simp [Set.mem_setOf_eq]
      have h2 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h2; simp at h2; exact h2
    | discreteSeriesPlus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | discreteSeriesMinus m hm =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (-1 : ℤ) ∈ ({x : ℤ | x ≤ -1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [hkt] at h1; simp at h1; omega
    | limitDiscretePlus =>
      exfalso; simp only [kTypes] at hkt
      have h1 : (1 : ℤ) ∈ ({x : ℤ | x ≥ 1 ∧ x % 2 = 1} : Set ℤ) := by simp
      rw [← hkt] at h1; simp at h1
    | limitDiscreteMinus => left; rfl

/--
[GKModule.IsIsomorphicGK.symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SL2Representations.lean)
-/
@[path]
private lemma symm_eq
  [LieRing 𝔤]
  [LieAlgebra ℂ 𝔤]
  [Group K]
  {𝔨 : LieSubalgebra ℂ 𝔤}
  {Ad : K →* (𝔤 →ₗ[ℂ] 𝔤)}
  [AddCommGroup V]
  [Module ℂ V]
  [LieRingModule 𝔤 V]
  [LieModule ℂ 𝔤 V]
  [AddCommGroup W]
  [Module ℂ W]
  [LieRingModule 𝔤 W]
  [LieModule ℂ 𝔤 W]
  {M : GKModule 𝔤 K 𝔨 Ad V}
  {N : GKModule 𝔤 K 𝔨 Ad W}
-- given
  (h : M.IsIsomorphicGK N) :
-- imply
  N.IsIsomorphicGK M := by
-- proof
  apply GKModule.IsIsomorphicGK.symm h


-- created on 2026-10-23
-- updated on 2026-10-24
