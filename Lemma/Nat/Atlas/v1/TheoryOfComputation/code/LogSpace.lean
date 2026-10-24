import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.LogSpace
open SpaceComplexity TuringMachine LogSpace
open TuringMachine


namespace LogSpace

/--
[nl_config_compute](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma nl_config_compute
  {NLComputes_cd NLDecides_pathd : ℕ → Prop}
  {d : ℕ}
-- given
  (thm_cd_to_pathd_succ : ∀ d, NLComputes_cd d → NLDecides_pathd (d + 1))
  (counting_to_cd : ∀ d, NLDecides_pathd d → NLComputes_cd d)
  (h : NLComputes_cd d) :
-- imply
  NLComputes_cd (d + 1) :=
-- proof
  counting_to_cd (d + 1) (thm_cd_to_pathd_succ d h)

end LogSpace

namespace LogSpace

/--
[step_eq_of_isHaltConfig](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma step_eq_of_isHaltConfig
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TuringMachine.TM Q Γ}
  {c : TuringMachine.Config Q Γ}
-- given
  (h : M.isHaltConfig c) :
-- imply
  M.step c = c := by
-- proof
  unfold TuringMachine.TM.step
  simp only [TuringMachine.TM.isHaltConfig, TuringMachine.TM.isAcceptConfig,
    TuringMachine.TM.isRejectConfig] at h
  obtain h | h <;> simp [h] := h

end LogSpace

namespace LogSpace

/--
[run_eq_of_isHaltConfig](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma run_eq_of_isHaltConfig
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TuringMachine.TM Q Γ}
  {c : TuringMachine.Config Q Γ}
  {n m : ℕ}
-- given
  (hn : n ≤ m)
  (h : M.isHaltConfig (M.run c n)) :
-- imply
  M.run c m = M.run c n := by
-- proof
  induction m with
  | zero => simp [Nat.le_zero.mp hn]
  | succ m ih =>
    by_cases hle : n ≤ m
    · simp only [TuringMachine.TM.run]
      rw [ih hle]; exact step_eq_of_isHaltConfig M _ h
    · have : n = m + 1 := by omega
      subst this; rfl

end LogSpace

namespace LogSpace

/--
[isHaltConfig_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma isHaltConfig_mono
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TuringMachine.TM Q Γ}
  {c : TuringMachine.Config Q Γ}
  {n m : ℕ}
-- given
  (hn : n ≤ m)
  (h : M.isHaltConfig (M.run c n)) :
-- imply
  M.isHaltConfig (M.run c m) := by
-- proof
  rw [run_eq_of_isHaltConfig M c hn h]; exact h

end LogSpace

namespace LogSpace

/--
[space_bounded_decider_poly_time](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma space_bounded_decider_poly_time
  {Q Γ : Type}
  [DecidableEq Q]
  [Fintype Q]
  [Fintype Γ]
  {M : TuringMachine.TM Q Γ}
  {g : ℕ → ℕ}
-- given
  (hSpace : TMRunsInSpace M g) :
-- imply
  ∃ (t : ℕ → ℕ) (K : ℕ), M.runsInTime t ∧ 0 < K ∧ ∀ n, t n ≤ K * 2 ^ (K * g n) := by
-- proof
  classical
  set qc := Fintype.card Q
  set gc := Fintype.card Γ
  set K := max (qc * gc) (Nat.clog 2 (2 * gc)) + 1
  have hK_pos : 0 < K := by omega
  have hK_ge_qc_gc : qc * gc < K := by omega
  have hK_ge_clog : Nat.clog 2 (2 * gc) < K := by omega
  have hgc_bound : 2 * gc ≤ 2 ^ K :=
    (Nat.le_pow_clog (by norm_num) (2 * gc)).trans
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hgc_le : gc ≤ 2 ^ (K - 1) := by
    have h2 : K = (K - 1) + 1 := by omega
    rw [h2, pow_succ] at hgc_bound; omega
  have hexp_ge : ∀ n : ℕ, n + 2 ≤ 2 ^ (n + 1) := by
    intro n; induction n with
    | zero => norm_num
    | succ n ih =>
      calc n + 3 ≤ (n + 2) + (n + 2) := by omega
        _ ≤ 2 ^ (n + 1) + 2 ^ (n + 1) := by omega
        _ = 2 ^ (n + 2) := by ring
  have hConfigBound : ∀ s, qc * (s + 1) * gc ^ (s + 1) ≤ K * 2 ^ (K * s) := by
    intro s
    obtain _ | s := s
    · simp; omega
    ·
      have hexp1 : s + 1 + (K - 1) * (s + 1) = K * (s + 1) := by
        have hK1 : K - 1 + 1 = K := Nat.succ_pred_eq_of_pos hK_pos
        have : s + 1 + (K - 1) * (s + 1) = (K - 1 + 1) * (s + 1) := by ring
        rw [this, hK1]
      calc qc * (s + 1 + 1) * gc ^ (s + 1 + 1)
        = qc * (s + 2) * (gc * gc ^ (s + 1)) := by ring
        _ ≤ qc * 2 ^ (s + 1) * (gc * (2 ^ (K - 1)) ^ (s + 1)) := by
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul_left _ (hexp_ge s)
          · exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hgc_le _)
        _ = qc * gc * (2 ^ (s + 1) * 2 ^ ((K - 1) * (s + 1))) := by ring
        _ = qc * gc * 2 ^ (s + 1 + (K - 1) * (s + 1)) := by rw [← pow_add]
        _ = qc * gc * 2 ^ (K * (s + 1)) := by rw [hexp1]
        _ ≤ K * 2 ^ (K * (s + 1)) := Nat.mul_le_mul_right _ (by omega)
  refine ⟨fun n => K * 2 ^ (K * g n), K, ?_, hK_pos, fun n => le_refl _⟩
  intro w
  set N := K * 2 ^ (K * g w.length) with hN_def
  by_contra h_not_halt
  obtain ⟨n₀, hn₀⟩ := hSpace.1 w
  have hN_lt : N < n₀ := by
    by_contra hle; push Not at hle
    exact h_not_halt (isHaltConfig_mono M (M.initConfig w) hle hn₀)
  have h_none : ∀ k, k ≤ N → ¬M.isHaltConfig (M.runOnInput w k) :=
    fun k hk hH => h_not_halt (isHaltConfig_mono M (M.initConfig w) hk hH)
  set S := TMSpaceUsed M w N
  have hS_le : S ≤ g w.length := by
    calc TMSpaceUsed M w N
      ≤ TMSpaceUsed M w n₀ := by
        unfold TMSpaceUsed
        exact Finset.card_le_card
          (Finset.image_subset_image (Finset.range_mono (by exact Nat.succ_le_succ (Nat.le_of_lt hN_lt))))
      _ ≤ g w.length := hSpace.2 w n₀ hn₀
  set visited := (Finset.range (N + 1)).image (fun k => (M.runOnInput w k).headPos)
  have hvc : visited.card = S := rfl
  have h_vis : ∀ k, k ≤ N → (M.runOnInput w k).headPos ∈ visited :=
    fun k hk => Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr (by omega), rfl⟩
  set enum := visited.equivFinOfCardEq hvc
  let proj : Fin (N + 1) → Q × Fin (S + 1) × (Fin (S + 1) → Γ) := fun ⟨k, hk⟩ =>
    let c := M.runOnInput w k
    (c.state, (enum ⟨c.headPos, h_vis k (by omega)⟩).castSucc,
      fun i => if hi : i.val < S then c.tape (enum.symm ⟨i.val, hi⟩).val else c.tape 0)
  have hcard : Fintype.card (Q × Fin (S + 1) × (Fin (S + 1) → Γ)) <
    Fintype.card (Fin (N + 1)) := by
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_fun]
    show qc * ((S + 1) * gc ^ (S + 1)) < N + 1
    calc qc * ((S + 1) * gc ^ (S + 1))
      = qc * (S + 1) * gc ^ (S + 1) := by ring
      _ ≤ K * 2 ^ (K * S) := hConfigBound S
      _ ≤ K * 2 ^ (K * g w.length) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_left K hS_le)
      _ = N := rfl
      _ < N + 1 := by omega
  obtain ⟨⟨k₁, hk₁⟩, ⟨k₂, hk₂⟩, hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt proj hcard
  simp only [proj, Prod.mk.injEq] at heq
  obtain ⟨hSt, hHd, hTp⟩ := heq
  have hHead : (M.runOnInput w k₁).headPos = (M.runOnInput w k₂).headPos := by
    simp only [Fin.castSucc_inj] at hHd
    exact congr_arg Subtype.val (enum.injective hHd)
  have hTape_eq : (M.runOnInput w k₁).tape = (M.runOnInput w k₂).tape := by
    funext p
    by_cases hp : p ∈ visited
    ·
      set idx := enum ⟨p, hp⟩
      have htf := congr_fun hTp ⟨idx.val, by omega⟩
      simp only [idx.isLt, dite_true] at htf
      have h1 : (↑(enum.symm ⟨idx.val, idx.isLt⟩) : ↥visited).val = p := by
        show (enum.symm (enum ⟨p, hp⟩)).val = p; simp
      unfold TuringMachine.TM.runOnInput at htf ⊢; rw [h1] at htf; exact htf
    ·
      have hp' : ∀ m, m < N + 1 → (M.runOnInput w m).headPos ≠ p := by
        intro m hm heq
        exact hp (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm, heq⟩)
      suffices haux : ∀ k, k ≤ N → (M.runOnInput w k).tape p = (M.initConfig w).tape p by
        rw [haux k₁ (by omega), haux k₂ (by omega)]
      intro k hk
      unfold TuringMachine.TM.runOnInput
      induction k with
      | zero => rfl
      | succ k ih =>
        show (M.step (M.run (M.initConfig w) k)).tape p = (M.initConfig w).tape p
        have hkp : (M.run (M.initConfig w) k).headPos ≠ p := hp' k (by omega)
        unfold TuringMachine.TM.step
        split_ifs with hh
        · exact ih (by omega)
        · simp only
          rw [Function.update_of_ne (Ne.symm hkp)]
          exact ih (by omega)
  have hcfg : M.runOnInput w k₁ = M.runOnInput w k₂ := by
    have : ∀ (c : Config Q Γ), c = ⟨c.state, c.headPos, c.tape⟩ := fun c => by cases c; rfl
    rw [this (M.runOnInput w k₁), this (M.runOnInput w k₂), hSt, hHead, hTape_eq]
  have hk_ne : k₁ ≠ k₂ := fun h => hne (Fin.ext h)
  obtain h_lt | h_lt := Nat.lt_or_gt_of_ne hk_ne
  · exact (SpaceComplexity.not_halts_of_config_repeat M w k₁ k₂ h_lt hcfg
    (h_none k₁ (by omega))) (hSpace.1 w)
  · exact (SpaceComplexity.not_halts_of_config_repeat M w k₂ k₁ h_lt hcfg.symm
    (h_none k₂ (by omega))) (hSpace.1 w)

end LogSpace

namespace LogSpace

/--
[l_subset_p](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/LogSpace.lean)
-/
@[path]
lemma l_subset_p
  {Γ : Type}
  [Fintype Γ]
  {A : Set (List Γ)}
-- given
  (h : InL A) :
-- imply
  TuringMachine.InP A := by
-- proof
  unfold InL InSPACE at h
  obtain ⟨Q, hFinQ, hDecEq, M, hLang, g, hgBound, hSpace⟩ := h
  letI := hFinQ; letI := hDecEq
  have hDecides : M.decides A := ⟨hSpace.1, hLang⟩
  obtain ⟨c_bound, n₀, hc_pos, hgBoundFn⟩ := hgBound
  obtain ⟨t, K, hRunsInTime, hK_pos, htBound⟩ :=
    space_bounded_decider_poly_time M g hSpace
  use K * c_bound + 1
  exact ⟨Q, inferInstance, hDecEq, M, t, hDecides, hRunsInTime,
    ⟨K, max n₀ 1, hK_pos, fun n hn => by
      dsimp only at hn ⊢
      have hn₀ : n₀ ≤ n := le_of_max_le_left hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have hn0 : n ≠ 0 := by omega
      have hg_le : g n ≤ c_bound * Nat.log 2 n := by
        have := hgBoundFn n hn₀; simp only [log] at this; exact this
      calc t n ≤ K * 2 ^ (K * g n) := htBound n
        _ ≤ K * 2 ^ (K * (c_bound * Nat.log 2 n)) := by
          apply Nat.mul_le_mul_left
          apply Nat.pow_le_pow_right (by norm_num : 1 ≤ 2)
          apply Nat.mul_le_mul_left
          exact hg_le
        _ = K * (2 ^ Nat.log 2 n) ^ (K * c_bound) := by
          rw [← pow_mul]; congr 1
          rw [mul_comm c_bound, ← mul_assoc, mul_comm K, mul_assoc]
        _ ≤ K * n ^ (K * c_bound) :=
          Nat.mul_le_mul_left K (Nat.pow_le_pow_left (Nat.pow_log_le_self 2 hn0) _)
        _ ≤ K * n ^ (K * c_bound + 1) :=
          Nat.mul_le_mul_left K (Nat.pow_le_pow_right hn1 (Nat.le_succ _))⟩⟩

end LogSpace


-- created on 2026-10-23
