import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.SpaceComplexity.Part7
open Computability TuringMachine SpaceComplexity
open TuringMachine
open NPCompleteness


namespace SpaceComplexity

/--
[step_halted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma step_halted
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
-- given
  (hc : M.isHaltConfig c) :
-- imply
  M.step c = c := by
-- proof
  unfold TM.step TM.isHaltConfig TM.isAcceptConfig TM.isRejectConfig at *
  simp [hc]

end SpaceComplexity

namespace SpaceComplexity

/--
[run_halted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma run_halted
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {k : ℕ}
-- given
  (hk : M.isHaltConfig (M.run c k)) :
-- imply
  ∀ m, k ≤ m → M.run c m = M.run c k := by
-- proof
  intro m hm
  induction m with
  | zero =>
    have : k = 0 := by omega
    subst this; rfl
  | succ m ih =>
    by_cases hkm : k ≤ m
    · simp only [TM.run]
      rw [ih hkm]
      exact step_halted M _ hk
    · have : k = m + 1 := by omega
      subst this
      rfl

end SpaceComplexity

namespace SpaceComplexity

/--
[tmSpaceUsed_le_steps](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tmSpaceUsed_le_steps
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {w : List Γ}
  {n : ℕ} :
-- imply
  TMSpaceUsed M w n ≤ n + 1 := by
-- proof
  unfold TMSpaceUsed
  calc Finset.card ((Finset.range (n + 1)).image (fun k => (M.runOnInput w k).headPos))
    ≤ (Finset.range (n + 1)).card := Finset.card_image_le
    _ = n + 1 := Finset.card_range (n + 1)

end SpaceComplexity

namespace SpaceComplexity

/--
[tmSpaceUsed_halted_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tmSpaceUsed_halted_eq
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {w : List Γ}
  {k n : ℕ}
-- given
  (hk : M.isHaltConfig (M.runOnInput w k))
  (hkn : k ≤ n) :
-- imply
  TMSpaceUsed M w n = TMSpaceUsed M w k := by
-- proof
  unfold TMSpaceUsed TM.runOnInput
  congr 1
  ext p
  simp only [Finset.mem_image, Finset.mem_range]
  constructor
  · rintro ⟨j, hj, hjp⟩
    by_cases hjk : j ≤ k
    · exact ⟨j, by omega, hjp⟩
    · simp only [not_le] at hjk
      have : M.run (M.initConfig w) j = M.run (M.initConfig w) k :=
        run_halted M _ k hk j (by omega)
      rw [this] at hjp
      exact ⟨k, by omega, hjp⟩
  · rintro ⟨j, hj, hjp⟩
    exact ⟨j, by omega, hjp⟩

end SpaceComplexity

namespace SpaceComplexity

/--
[TIME_subset_SPACE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma TIME_subset_SPACE
  {Γ : Type}
  {t : ℕ → ℕ}
  {A : Set (List Γ)}
-- given
  (ht : ∀ n, n ≤ t n) :
-- imply
  TuringMachine.InTIME t A → InSPACE t A := by
-- proof
  intro ⟨Q, _, hDecEq, M, t', hDec, hTime, hBigO⟩
  refine ⟨Q, inferInstance, hDecEq, M, ?_, ?_⟩
  · exact hDec.2
  ·
    refine ⟨fun n => t' n + 1, ?_, ?_⟩
    ·
      obtain ⟨c, n₀, hc, hBound⟩ := hBigO
      refine ⟨c + 1, max n₀ 1, by omega, ?_⟩
      intro n hn
      have hn₀ : n₀ ≤ n := le_of_max_le_left hn
      have hn1 : 1 ≤ n := le_of_max_le_right hn
      have ht' := hBound n hn₀
      have htn : 1 ≤ t n := le_trans hn1 (ht n)
      simp only [Nat.add_mul, Nat.one_mul] at *
      omega
    ·
      constructor
      · exact hDec.1
      · intro w n hHalt
        have hHaltT : M.isHaltConfig (M.runOnInput w (t' w.length)) := hTime w
        by_cases hn : n ≤ t' w.length
        · calc TMSpaceUsed M w n
          ≤ n + 1 := tmSpaceUsed_le_steps M w n
          _ ≤ t' w.length + 1 := by omega
        · simp only [not_le] at hn
          calc TMSpaceUsed M w n
            = TMSpaceUsed M w (t' w.length) :=
              tmSpaceUsed_halted_eq M w (t' w.length) n hHaltT (by omega)
            _ ≤ t' w.length + 1 := tmSpaceUsed_le_steps M w (t' w.length)

end SpaceComplexity

namespace SpaceComplexity

/--
[P_subset_PSPACE](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma P_subset_PSPACE
  {Γ : Type}
  {A : Set (List Γ)} :
-- imply
  TuringMachine.InP A → InPSPACE A := by
-- proof
  intro ⟨k, hTIME⟩
  use k + 1
  apply TIME_subset_SPACE (fun n => n ^ (k + 1)) A
  ·
    intro n
    by_cases hn : n = 0
    · simp [hn]
    · calc n = n ^ 1 := (Nat.pow_one n).symm
      _ ≤ n ^ (k + 1) := Nat.pow_le_pow_right (Nat.pos_of_ne_zero hn) (by omega)
  ·
    obtain ⟨Q, _, hDecEq, M, t', hDec, hTime, c, n₀, hc, hBound⟩ := hTIME
    refine ⟨Q, inferInstance, hDecEq, M, t', hDec, hTime, c, max n₀ 1, hc, ?_⟩
    intro n hn
    have hn₀ : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    calc t' n ≤ c * n ^ k := hBound n hn₀
      _ ≤ c * n ^ (k + 1) := by
        apply Nat.mul_le_mul_left
        exact Nat.pow_le_pow_right (by omega) (by omega)

end SpaceComplexity

namespace SpaceComplexity

/--
[run_periodic_of_config_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma run_periodic_of_config_repeat
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c₀ : Config Q Γ}
  {i j : ℕ}
-- given
  (_hij : i < j)
  (hrepeat : M.run c₀ i = M.run c₀ j) :
-- imply
  ∀ k, M.run c₀ (i + k) = M.run c₀ (j + k) := by
-- proof
  intro k
  induction k with
  | zero => simp [hrepeat]
  | succ k ih =>
    show M.step (M.run c₀ (i + k)) = M.step (M.run c₀ (j + k))
    rw [ih]

end SpaceComplexity

namespace SpaceComplexity

/--
[not_halts_of_config_repeat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma not_halts_of_config_repeat
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {w : List Γ}
  {i j : ℕ}
-- given
  (hij : i < j)
  (hrepeat : M.runOnInput w i = M.runOnInput w j)
  (hNotHalt : ¬M.isHaltConfig (M.runOnInput w i)) :
-- imply
  ¬M.halts w := by
-- proof
  intro ⟨n, hn⟩
  unfold TM.runOnInput at hrepeat hNotHalt hn
  have hperiodic := run_periodic_of_config_repeat M (M.initConfig w) i j hij hrepeat
  have hjsub : 1 ≤ j - i := by omega
  have hperiodic_shift : ∀ m : ℕ,
    M.run (M.initConfig w) (i + m * (j - i)) = M.run (M.initConfig w) i := by
    intro m
    induction m with
    | zero => simp
    | succ m ihm =>
      have hle : i ≤ j := Nat.le_of_lt hij
      have hstep : i + (m + 1) * (j - i) = j + m * (j - i) := by
        rw [Nat.succ_mul]; omega
      rw [show i + (m + 1) * (j - i) = j + m * (j - i) from hstep]
      rw [← hperiodic (m * (j - i)), ihm]
  by_cases hni : n < i
  ·
    have h := run_halted M (M.initConfig w) n hn i (by omega)
    rw [h] at hNotHalt
    exact hNotHalt hn
  ·
    push Not at hni
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n ≤ i + m * (j - i) := by
      use n
      calc n = n * 1 := (Nat.mul_one n).symm
        _ ≤ n * (j - i) := Nat.mul_le_mul_left n hjsub
        _ ≤ i + n * (j - i) := Nat.le_add_left _ _
    have hNotHalt_m : ¬M.isHaltConfig (M.run (M.initConfig w) (i + m * (j - i))) := by
      rw [hperiodic_shift m]; exact hNotHalt
    have h := run_halted M (M.initConfig w) n hn (i + m * (j - i)) hm
    rw [h] at hNotHalt_m
    exact hNotHalt_m hn
end SpaceComplexity
namespace SpaceComplexity

end SpaceComplexity

namespace SpaceComplexity

/--
[tape_unchanged_at_unvisited](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tape_unchanged_at_unvisited
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c₀ : Config Q Γ}
  {n : ℕ}
  {p : ℤ}
-- given
  (hp : ∀ k, k ≤ n → (M.run c₀ k).headPos ≠ p) :
-- imply
  (M.run c₀ n).tape p = c₀.tape p := by
-- proof
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    simp only [TM.run]
    have ih' := ih (fun k hk => hp k (by omega))
    have hp_n : (M.run c₀ n).headPos ≠ p := hp n (by omega)
    unfold TM.step; split
    · exact ih'
    · simp only; rw [Function.update_of_ne hp_n.symm]; exact ih'

end SpaceComplexity

namespace SpaceComplexity

/--
[configs_eq_of_encode_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma configs_eq_of_encode_eq
  {Q Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c₀ : Config Q Γ}
  {i j N : ℕ}
  {S : Finset ℤ}
-- given
  (hiN : i ≤ N)
  (hjN : j ≤ N)
  (hS : ∀ k, k ≤ N → (M.run c₀ k).headPos ∈ S)
  (hstate : (M.run c₀ i).state = (M.run c₀ j).state)
  (hhead : (M.run c₀ i).headPos = (M.run c₀ j).headPos)
  (htape : ∀ p ∈ S, (M.run c₀ i).tape p = (M.run c₀ j).tape p) :
-- imply
  M.run c₀ i = M.run c₀ j := by
-- proof
  have : (M.run c₀ i).tape = (M.run c₀ j).tape := by
    funext p
    by_cases hp : p ∈ S
    · exact htape p hp
    · rw [tape_unchanged_at_unvisited M c₀ i p
      (fun k hk habs => hp (habs ▸ hS k (by omega))),
      tape_unchanged_at_unvisited M c₀ j p
      (fun k hk habs => hp (habs ▸ hS k (by omega)))]
  cases hi : M.run c₀ i; cases hj : M.run c₀ j; simp_all

end SpaceComplexity

/--
[SpaceComplexity.SPACE_subset_TIME_exp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma SpaceComplexity.SPACE_subset_TIME_exp
  {Γ : Type}
  [Fintype Γ]
  {t : ℕ → ℕ}
  {A : Set (List Γ)}
-- given
  (ht : ∀ n, n ≤ t n) :
-- imply
  SpaceComplexity.InSPACE t A → ∃ c : ℕ, TuringMachine.InTIME (fun n => c ^ t n) A := by
-- proof
  intro ⟨Q, hFinQ, hDecEq, M, hLang, g, hBound, hDecider, hSpaceBound⟩
  obtain ⟨c_bound, n₀, hc_pos, hBoundIneq⟩ := hBound
  set cardQ := @Fintype.card Q hFinQ with hcardQ_def
  set cardΓ := Fintype.card Γ with hcardΓ_def
  set c₀ := (cardΓ + 1) ^ (c_bound + 1) + 1 with hc₀_def
  use c₀ ^ 2
  set tb : ℕ → ℕ := fun n => cardQ * (g n + 1) * cardΓ ^ (g n + 1) with htb_def
  refine ⟨Q, hFinQ, hDecEq, M, tb, ⟨hDecider, hLang⟩, ?_, ?_⟩
  ·
    intro w
    set N := tb w.length with hN_def
    set s := g w.length with hs_def
    obtain ⟨n_halt, hn_halt⟩ := hDecider w
    have hspace : SpaceComplexity.TMSpaceUsed M w n_halt ≤ s := hSpaceBound w n_halt hn_halt
    set S := (Finset.range (n_halt + 1)).image (fun k => (M.runOnInput w k).headPos) with hS_def
    by_cases h_halts_early : ∃ m, m ≤ N ∧ M.isHaltConfig (M.runOnInput w m)
    · obtain ⟨m, hm, hHalt_m⟩ := h_halts_early
      unfold TM.runOnInput at hHalt_m ⊢
      have := SpaceComplexity.run_halted M (M.initConfig w) m hHalt_m N hm
      rw [this]; exact hHalt_m
    · exfalso; push_neg at h_halts_early
      have hn_gt : N < n_halt := by
        by_contra h; push_neg at h; exact h_halts_early n_halt h hn_halt
      have hS_card : S.card ≤ s := hspace
      have hS_mem : ∀ k, k ≤ N → (M.runOnInput w k).headPos ∈ S := by
        intro k hk; simp only [S, Finset.mem_image, Finset.mem_range]
        exact ⟨k, by omega, rfl⟩
      let encode : Fin (N + 1) → Q × ↥S × (↥S → Γ) := fun ⟨k, hk⟩ =>
        ((M.runOnInput w k).state,
          ⟨(M.runOnInput w k).headPos, hS_mem k (by omega)⟩,
          fun ⟨p, _⟩ => (M.runOnInput w k).tape p)
      have hcod_le : @Fintype.card (Q × ↥S × (↥S → Γ)) _ ≤ N := by
        simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_coe]
        calc @Fintype.card Q hFinQ * (S.card * cardΓ ^ S.card)
          ≤ cardQ * ((s + 1) * cardΓ ^ (s + 1)) := by
            apply Nat.mul_le_mul_left
            apply Nat.mul_le_mul (by omega)
            have : 0 < cardΓ := Fintype.card_pos_iff.mpr ⟨M.blank⟩
            exact Nat.pow_le_pow_right this (by omega)
          _ = N := by simp only [N, tb, s]; rw [Nat.mul_assoc]
      have hpig : @Fintype.card (Q × ↥S × (↥S → Γ)) _ < Fintype.card (Fin (N + 1)) := by
        rw [Fintype.card_fin]; omega
      obtain ⟨⟨i, hi⟩, ⟨j, hj⟩, hij, hencode⟩ :=
        Fintype.exists_ne_map_eq_of_card_lt encode hpig
      simp only [encode, Prod.mk.injEq] at hencode
      obtain ⟨hstate, hhead_sub, htape_fn⟩ := hencode
      have hhead : (M.runOnInput w i).headPos = (M.runOnInput w j).headPos :=
        congr_arg Subtype.val hhead_sub
      have htape : ∀ p ∈ S, (M.runOnInput w i).tape p = (M.runOnInput w j).tape p :=
        fun p hp => congr_fun htape_fn ⟨p, hp⟩
      unfold TM.runOnInput at hstate hhead htape
      have hconfig := SpaceComplexity.configs_eq_of_encode_eq M (M.initConfig w)
        i j N (by omega) (by omega) S (fun k hk => hS_mem k hk)
        hstate hhead (fun p hp => htape p hp)
      have hij_ne : i ≠ j := fun h => hij (Fin.ext h)
      obtain hi_lt | hj_lt := Nat.lt_or_gt_of_ne hij_ne
      · exact SpaceComplexity.not_halts_of_config_repeat M w i j hi_lt
        (by unfold TM.runOnInput; exact hconfig)
        (by unfold TM.runOnInput; exact h_halts_early i (by omega))
        (hDecider w)
      · exact SpaceComplexity.not_halts_of_config_repeat M w j i hj_lt
        (by unfold TM.runOnInput; exact hconfig.symm)
        (by unfold TM.runOnInput; exact h_halts_early j (by omega))
        (hDecider w)
  ·
    refine ⟨cardQ * (c_bound + 1) + 1, max n₀ 1, by omega, fun n hn => ?_⟩
    have hn₀ : n₀ ≤ n := le_of_max_le_left hn
    have hn1 : 1 ≤ n := le_of_max_le_right hn
    have htn : 1 ≤ t n := le_trans hn1 (ht n)
    have hgn : g n ≤ c_bound * t n := hBoundIneq n hn₀
    have hgn1 : g n + 1 ≤ (c_bound + 1) * t n := by
      rw [Nat.add_mul]; omega
    have hc₀_ge2 : 2 ≤ c₀ := by
      have := Nat.one_le_pow (c_bound + 1) (cardΓ + 1) (by omega)
      omega
    have hc₀_ge : (cardΓ + 1) ^ (c_bound + 1) ≤ c₀ := by omega
    have hc₀_pow_ge_t : t n ≤ c₀ ^ t n := by
      calc t n ≤ 2 ^ t n := Nat.lt_two_pow_self.le
        _ ≤ c₀ ^ t n := Nat.pow_le_pow_left hc₀_ge2 (t n)
    have hc₀_pow_ge_gamma : cardΓ ^ ((c_bound + 1) * t n) ≤ c₀ ^ t n := by
      calc cardΓ ^ ((c_bound + 1) * t n)
        ≤ (cardΓ + 1) ^ ((c_bound + 1) * t n) :=
          Nat.pow_le_pow_left (Nat.le_succ _) _
        _ = ((cardΓ + 1) ^ (c_bound + 1)) ^ t n := by rw [pow_mul]
        _ ≤ c₀ ^ t n := Nat.pow_le_pow_left hc₀_ge (t n)
    have hpow_sq : t n * cardΓ ^ ((c_bound + 1) * t n) ≤ (c₀ ^ 2) ^ t n := by
      rw [show (c₀ ^ 2) ^ t n = c₀ ^ t n * c₀ ^ t n from by
        rw [← pow_mul, show 2 * t n = t n + t n from by omega, pow_add]]
      exact Nat.mul_le_mul hc₀_pow_ge_t hc₀_pow_ge_gamma
    have hstep1 : tb n ≤ cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) := by
      apply Nat.mul_le_mul
      · exact Nat.mul_le_mul_left _ hgn1
      · have : 0 < cardΓ := Fintype.card_pos_iff.mpr ⟨M.blank⟩
        exact Nat.pow_le_pow_right this hgn1
    have hstep2 : cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) =
      cardQ * (c_bound + 1) * (t n * cardΓ ^ ((c_bound + 1) * t n)) := by
      simp only [Nat.mul_assoc]
    calc tb n
      ≤ cardQ * ((c_bound + 1) * t n) * cardΓ ^ ((c_bound + 1) * t n) := hstep1
      _ = cardQ * (c_bound + 1) * (t n * cardΓ ^ ((c_bound + 1) * t n)) := hstep2
      _ ≤ cardQ * (c_bound + 1) * (c₀ ^ 2) ^ t n := Nat.mul_le_mul_left _ hpow_sq
      _ ≤ (cardQ * (c_bound + 1) + 1) * (c₀ ^ 2) ^ t n := by
        apply Nat.mul_le_mul_right; omega

namespace SpaceComplexity

/--
[TIME_SPACE_relationship](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma TIME_SPACE_relationship
  {Γ : Type}
  [Fintype Γ]
  {t : ℕ → ℕ}
  {A : Set (List Γ)}
-- given
  (ht : ∀ n, n ≤ t n) :
-- imply
  (TuringMachine.InTIME t A → InSPACE t A) ∧ (InSPACE t A → ∃ c : ℕ, TuringMachine.InTIME (fun n => c ^ t n) A) :=
-- proof
  ⟨TIME_subset_SPACE t A ht, SPACE_subset_TIME_exp t A ht⟩
end SpaceComplexity
/-- **`NTIME(t(n)) ⊆ SPACE(t(n))`** (Sipser): a nondeterministic machine running in time
`t` can be simulated by a deterministic machine using space `t`. (Placeholder; proof
deferred.) -/
namespace SpaceComplexity
open NPCompleteness

end SpaceComplexity

namespace SpaceComplexity

/--
[IsBigO_of_le_eventually](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma IsBigO_of_le_eventually
  {f g₁ g₂ : ℕ → ℕ}
-- given
  (hf : TuringMachine.IsBigO f g₁)
  (hle : ∃ n₀, ∀ n, n₀ ≤ n → g₁ n ≤ g₂ n) :
-- imply
  TuringMachine.IsBigO f g₂ := by
-- proof
  obtain ⟨c, n₀, hc, hBound⟩ := hf
  obtain ⟨n₁, hle⟩ := hle
  refine ⟨c, max n₀ n₁, hc, fun n hn => ?_⟩
  have hn₀ : n₀ ≤ n := le_of_max_le_left hn
  have hn₁ : n₁ ≤ n := le_of_max_le_right hn
  calc f n ≤ c * g₁ n := hBound n hn₀
    _ ≤ c * g₂ n := Nat.mul_le_mul_left c (hle n hn₁)

end SpaceComplexity

namespace SpaceComplexity

/--
[InNTIME_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma InNTIME_mono
  {Γ : Type}
  {t₁ t₂ : ℕ → ℕ}
  {A : Set (List Γ)}
-- given
  (hle : ∃ n₀, ∀ n, n₀ ≤ n → t₁ n ≤ t₂ n)
  (h : TuringMachine.InNTIME t₁ A) :
-- imply
  TuringMachine.InNTIME t₂ A := by
-- proof
  obtain ⟨Q, _, hDecEq, M, t', hDec, hTime, hBigO⟩ := h
  exact ⟨Q, inferInstance, hDecEq, M, t', hDec, hTime, IsBigO_of_le_eventually hBigO hle⟩

end SpaceComplexity

namespace SpaceComplexity

/--
[le_pow_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma le_pow_of_pos
  {k : ℕ}
  {n : ℕ}
-- given
  (hk : 1 ≤ k) :
-- imply
  n ≤ n ^ k := by
-- proof
  obtain rfl | hn := Nat.eq_or_lt_of_le (Nat.zero_le n)
  · simp
  · calc n = n ^ 1 := (Nat.pow_one n).symm
    _ ≤ n ^ k := Nat.pow_le_pow_right hn hk

end SpaceComplexity

namespace SpaceComplexity

/--
[QBF.existsPlayerWins_iff_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma QBF.existsPlayerWins_iff_eval
  {σ : BoolAssignment}
  {ψ : QBF} :
-- imply
  ψ.ExistsPlayerWins σ ↔ ψ.eval σ = true := by
-- proof
  induction ψ generalizing σ with
  | body φ => simp [QBF.ExistsPlayerWins, QBF.eval]
  | exists_ x ψ ih =>
    simp only [QBF.ExistsPlayerWins, QBF.eval]
    rw [ih (Function.update σ x true), ih (Function.update σ x false)]
    simp [Bool.or_eq_true]
  | forall_ x ψ ih =>
    simp only [QBF.ExistsPlayerWins, QBF.eval]
    rw [ih (Function.update σ x true), ih (Function.update σ x false)]
    simp [Bool.and_eq_true]

end SpaceComplexity

namespace SpaceComplexity

/--
[QBF.existsPlayerWins_iff_isTrue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma QBF.existsPlayerWins_iff_isTrue
  {ψ : QBF} :
-- imply
  ψ.ExistsPlayerWins (fun _ => false) ↔ ψ.IsTrue :=
-- proof
  ψ.existsPlayerWins_iff_eval (fun _ => false)

end SpaceComplexity

namespace SpaceComplexity

/--
[formulaGameLanguage_eq_TQBF](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma formulaGameLanguage_eq_TQBF
-- imply
  {ψ : QBF | ψ.IsFullyQuantified ∧ ψ.ExistsPlayerWins (fun _ => false)} = TQBF := by
-- proof
  ext ψ
  simp only [Set.mem_setOf_eq, TQBF]
  constructor
  · rintro ⟨hfq, hw⟩
    exact ⟨hfq, ψ.existsPlayerWins_iff_isTrue.mp hw⟩
  · rintro ⟨hfq, ht⟩
    exact ⟨hfq, ψ.existsPlayerWins_iff_isTrue.mpr ht⟩

end SpaceComplexity

namespace SpaceComplexity

/--
[NTM.canYield_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma NTM.canYield_zero
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : NTM Q Γ}
  {c₁ c₂ : Config Q Γ} :
-- imply
  M.CanYield c₁ c₂ 0 ↔ c₁ = c₂ := by
-- proof
  simp [NTM.CanYield]

end SpaceComplexity

namespace SpaceComplexity

/--
[NTM.canYield_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma NTM.canYield_succ
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : NTM Q Γ}
  {c₁ c₂ : Config Q Γ}
  {b : ℕ} :
-- imply
  M.CanYield c₁ c₂ b → M.CanYield c₁ c₂ (b + 1) := by
-- proof
  intro h
  induction b generalizing c₁ with
  | zero =>
    simp [NTM.CanYield] at h
    simp [NTM.CanYield, h]
  | succ n ih =>
    simp only [NTM.CanYield] at h ⊢
    obtain rfl | ⟨c_mid, hstep, hrest⟩ := h
    · left; rfl
    · right; exact ⟨c_mid, hstep, ih c_mid hrest⟩

end SpaceComplexity

namespace SpaceComplexity

/--
[NTM.canYield_of_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma NTM.canYield_of_le
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : NTM Q Γ}
  {c₁ c₂ : Config Q Γ}
  {b b' : ℕ}
-- given
  (hle : b ≤ b')
  (h : M.CanYield c₁ c₂ b) :
-- imply
  M.CanYield c₁ c₂ b' := by
-- proof
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hle
  induction k with
  | zero => simpa using h
  | succ n ih =>
    rw [Nat.add_succ]
    exact M.canYield_succ c₁ c₂ _ (ih (by omega))
end SpaceComplexity
/-- **Core of Savitch's theorem** (Sipser, Theorem 8.5): given an NTM `N` running in
space `g`, construct a deterministic TM `M` recognizing the same language that decides
membership using space `O(g²)` via the recursive `CANYIELD` procedure. (Placeholder.) -/
namespace SpaceComplexity

end SpaceComplexity

namespace SpaceComplexity

/--
[tqbfNTM_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tqbfNTM_language
  {Γ : Type}
  [Inhabited Γ]
  [DecidableEq Γ]
  [Fintype Γ]
  {enc : QBFEncoding Γ} :
-- imply
  (tqbfNTM enc).language = tqbfLanguage enc := by
-- proof
  set M := tqbfNTM enc with M_def
  ext w
  simp only [NTM.language, Set.mem_setOf_eq, tqbfLanguage, Set.mem_setOf_eq]
  constructor
  ·
    intro ⟨hAlpha, branch, k, hValid, hAccept⟩
    have hNonBlank : ∀ s ∈ w, s ≠ (default : Γ) := fun s hs => hAlpha s hs
    have scanInv : ∀ i : ℕ, i ≤ w.length →
      (branch i).state = ((⟨0, by omega⟩ : Fin 3), w.take i) ∧
      (branch i).headPos = (i : ℤ) ∧
      (branch i).tape = (M.initConfig w).tape := by
      intro i hi
      induction i with
      | zero =>
        exact ⟨congr_arg Config.state hValid.1, congr_arg Config.headPos hValid.1,
          congr_arg Config.tape hValid.1⟩
      | succ n ih =>
        have hn : n < w.length := Nat.lt_of_succ_le hi
        obtain ⟨hS, hH, hT⟩ := ih (Nat.le_of_lt hn)
        have hNotHalt : ¬M.isHaltConfig (branch n) := by
          simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
          rw [hS]; intro h; rcases h with h | h <;> simp [TQBFState] at h
        have hStep := (hValid.2 n).1 hNotHalt
        have hRead : (branch n).tape (branch n).headPos = w.get ⟨n, hn⟩ := by
          rw [hT, hH]; simp [NTM.initConfig, M_def, tqbfNTM, show (0 : ℤ) ≤ (n : ℤ) from by omega,
            show (n : ℤ) < (w.length : ℤ) from by omega]
        have hSymNB : w.get ⟨n, hn⟩ ≠ (default : Γ) :=
          hNonBlank _ (List.get_mem w ⟨n, hn⟩)
        obtain ⟨_, q', b, d, hMem, hSt, hHd, hTp⟩ := hStep
        have hTrEq : (q', b, d) = ((⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]),
          w.get ⟨n, hn⟩, Direction.R) := by
          have h := hMem; rw [hS, hRead] at h
          simp only [M_def, tqbfNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff] at h
          exact h
        obtain ⟨hq', hb, hd⟩ : q' = (⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]) ∧
          b = w.get ⟨n, hn⟩ ∧ d = Direction.R :=
          ⟨congr_arg Prod.fst hTrEq, congr_arg (fun x => x.2.1) hTrEq,
            congr_arg (fun x => x.2.2) hTrEq⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hSt, hq', List.take_succ_eq_append_getElem hn]; simp [List.get_eq_getElem]
        · rw [hHd, hd, hH]; norm_cast
        · rw [hTp, hT, hH, hb, ← hRead, hT, hH]; exact Function.update_eq_self _ _
    obtain ⟨hS_end, hH_end, hT_end⟩ := scanInv w.length le_rfl
    rw [List.take_length] at hS_end
    have hNotHalt_end : ¬M.isHaltConfig (branch w.length) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
      rw [hS_end]; intro h; rcases h with h | h <;> simp [TQBFState] at h
    have hReadBlank : (branch w.length).tape (branch w.length).headPos = (default : Γ) := by
      rw [hT_end, hH_end]; simp [NTM.initConfig, M_def, tqbfNTM]
    have hStepEnd := (hValid.2 w.length).1 hNotHalt_end
    obtain ⟨_, q'', b'', d'', hMem'', hSt'', _, _⟩ := hStepEnd
    have hTransIn : (q'', b'', d'') ∈ M.δ ((⟨0, by omega⟩ : Fin 3), w) (default : Γ) := by
      have h := hMem''; rwa [hS_end, hReadBlank] at h
    have hNotAccBefore : ∀ i, i ≤ w.length → (branch i).state ≠ M.qAccept := by
      intro i hi hEq; have ⟨hSi, _, _⟩ := scanInv i hi
      rw [hSi] at hEq; simp [M_def, tqbfNTM, TQBFState] at hEq
    have hk_gt : k > w.length := by
      by_contra h; push_neg at h; exact hNotAccBefore k h hAccept
    have hHalt_next : M.isHaltConfig (branch (w.length + 1)) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM, hSt'']
      simp only [M_def, tqbfNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      split_ifs at hTransIn <;> (obtain ⟨rfl, -, -⟩ := hTransIn; simp [TQBFState])
    have hConst : ∀ j, j ≥ w.length + 1 → branch j = branch (w.length + 1) := by
      intro j hj; induction j with
      | zero => omega
      | succ m ihm =>
        by_cases hm : m ≥ w.length + 1
        · have heq := ihm hm
          exact ((hValid.2 m).2 (heq ▸ hHalt_next)).symm ▸ heq
        · push_neg at hm; congr 1; omega
    have hAccNext : (branch (w.length + 1)).state = M.qAccept := by
      have := hConst k (by omega); rw [← this]; exact hAccept
    have hq''_acc : q'' = ((⟨1, by omega⟩ : Fin 3), ([] : List Γ)) := by
      rw [hSt''] at hAccNext; exact hAccNext
    have hResultTrue : (match enc.decode w with
      | some φ => decide (φ.freeVars = ∅) && φ.eval (fun _ => false)
      | none => false) = true := by
      by_contra hFalse; push_neg at hFalse; simp only [Bool.not_eq_true] at hFalse
      simp only [M_def, tqbfNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      simp only [hFalse, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      obtain ⟨rfl, -, -⟩ := hTransIn
      simp [TQBFState] at hq''_acc
    cases hDec : enc.decode w with
    | none => simp [hDec] at hResultTrue
    | some ψ =>
      simp [hDec, Bool.and_eq_true] at hResultTrue
      exact ⟨ψ, enc.encode_decode w ψ hDec, hResultTrue.1, hResultTrue.2⟩
  ·
    intro ⟨ψ, hEncode, hTQBF⟩
    obtain ⟨hFQ, hTrue⟩ := hTQBF
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [M_def, tqbfNTM, NTM.inputAlpha, Set.mem_setOf_eq]
      exact fun heq => enc.blank_free ψ (hEncode ▸ heq ▸ hs)
    ·
      refine ⟨fun n =>
        if n ≤ w.length then
          ⟨((⟨0, by omega⟩ : Fin 3), w.take n), (n : ℤ), (M.initConfig w).tape⟩
        else
          ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), ((w.length : ℤ) + 1),
            Function.update (M.initConfig w).tape (↑w.length) default⟩,
        w.length + 1, ?_, ?_⟩
      ·
        constructor
        · simp [NTM.initConfig, M_def, tqbfNTM]
        · intro n; constructor
          ·
            intro hNotHalt
            simp only [NTM.step]; refine ⟨hNotHalt, ?_⟩
            by_cases hn_le : n ≤ w.length
            · by_cases hn_lt : n < w.length
              ·
                simp only [hn_le, ↓reduceIte]
                have hRead : (M.initConfig w).tape (↑n) = w.get ⟨n, hn_lt⟩ := by
                  simp [NTM.initConfig, M_def, tqbfNTM,
                    show (0 : ℤ) ≤ (n : ℤ) from by omega,
                    show (n : ℤ) < (w.length : ℤ) from by omega]
                have hSymNB : w.get ⟨n, hn_lt⟩ ≠ (default : Γ) := by
                  exact fun h => enc.blank_free ψ (hEncode ▸ h ▸ List.get_mem w ⟨n, hn_lt⟩)
                refine ⟨((⟨0, by omega⟩ : Fin 3), w.take n ++ [w.get ⟨n, hn_lt⟩]),
                  w.get ⟨n, hn_lt⟩, Direction.R, ?_, ?_, ?_, ?_⟩
                ·
                  show _ ∈ M.δ ((⟨0, _⟩, w.take n)) ((M.initConfig w).tape ↑n)
                  rw [hRead]
                  simp only [M_def, tqbfNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff]
                  simp only [List.get_eq_getElem]
                  rfl
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [List.take_succ_eq_append_getElem hn_lt]; simp [List.get_eq_getElem]
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]; norm_cast
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [← hRead]; exact (Function.update_eq_self ((↑n : ℤ)) _).symm
              ·
                have hn_eq : n = w.length := Nat.le_antisymm hn_le (by omega)
                subst hn_eq
                simp only [le_refl, ↓reduceIte, List.take_length]
                have hReadBl : (M.initConfig w).tape (↑w.length : ℤ) = (default : Γ) := by
                  simp [NTM.initConfig, M_def, tqbfNTM]
                have hDecW : enc.decode w = some ψ := by rw [← hEncode]; exact enc.decode_encode ψ
                have hResult : (match enc.decode w with
                  | some φ => decide (φ.freeVars = ∅) && φ.eval (fun _ => false)
                  | none => false) = true := by
                  rw [hDecW]
                  simp only [Bool.and_eq_true, decide_eq_true_eq]
                  exact ⟨hFQ, hTrue⟩
                refine ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), default, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, (by omega : (0 : Fin 3).val < 3)⟩, w)) ((M.initConfig w).tape ↑w.length)
                  rw [hReadBl]
                  simp only [M_def, tqbfNTM, ↓reduceIte, hResult, Set.mem_singleton_iff]
                  rfl
                · simp [show ¬(w.length + 1 ≤ w.length) from by omega]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false, Direction]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false]
            ·
              exfalso; apply hNotHalt
              simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM,
                show ¬(n ≤ w.length) from hn_le, ↓reduceIte]
              left; trivial
          ·
            intro hHalt
            by_cases hn_le : n ≤ w.length
            · exfalso; apply hHalt.elim <;> intro h <;>
              simp [NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM, hn_le, TQBFState] at h
            · simp [show ¬(n ≤ w.length) from hn_le, show ¬(n + 1 ≤ w.length) from by omega]
      ·
        simp only [NTM.isAcceptConfig, M_def, tqbfNTM, show ¬(w.length + 1 ≤ w.length) from by omega,
          ↓reduceIte]
set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in

end SpaceComplexity

namespace SpaceComplexity

/--
[tqbfNTM_runs_in_linear_space](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tqbfNTM_runs_in_linear_space
  {Γ : Type}
  [Inhabited Γ]
  [DecidableEq Γ]
  [Fintype Γ]
  {enc : QBFEncoding Γ} :
-- imply
  ∃ g : ℕ → ℕ, IsAsympBoundedBy g id ∧ (tqbfNTM enc).RunsInSpace g := by
-- proof
  refine ⟨fun n => n + 2, ?_, ?_⟩
  · exact ⟨2, 2, by omega, fun n hn => by simp [id]; omega⟩
  · set M := tqbfNTM enc with M_def
    intro w branch hValid
    have trans_right_wb : ∀ k, ¬M.isHaltConfig (branch k) →
      (branch (k + 1)).headPos = (branch k).headPos + 1 ∧
      (branch (k + 1)).tape = (branch k).tape := by
      intro k hNotHalt
      have hStep := (hValid.2 k).1 hNotHalt
      obtain ⟨_, q', b, d, hMem, _, hHd, hTp⟩ := hStep
      have h_facts : d = Direction.R ∧ b = (branch k).tape (branch k).headPos := by
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig,
          M_def, tqbfNTM] at hNotHalt
        push_neg at hNotHalt
        revert hMem; generalize (branch k).state = st
        generalize (branch k).tape (branch k).headPos = sym
        intro hMem
        match st with
        | (⟨0, _⟩, buf) =>
          simp only [M_def, tqbfNTM] at hMem
          split_ifs at hMem with h1 h2
          all_goals (
            have heq := Set.eq_of_mem_singleton hMem
            refine ⟨congr_arg (·.2.2) heq, ?_⟩
            have hb := congr_arg (·.2.1) heq
            simp at hb; first | exact hb | (rw [hb]; exact h1.symm))
        | (⟨1, _⟩, _) => exact absurd hMem (Set.notMem_empty _)
        | (⟨2, _⟩, _) => exact absurd hMem (Set.notMem_empty _)
      exact ⟨by rw [hHd, h_facts.1], by rw [hTp, h_facts.2, Function.update_eq_self]⟩
    have headPos_eq : ∀ k, (∀ j < k, ¬M.isHaltConfig (branch j)) →
      (branch k).headPos = ↑k := by
      intro k hk; induction k with
      | zero => simp [congr_arg Config.headPos hValid.1, NTM.initConfig]
      | succ n ih =>
        have := (trans_right_wb n (hk n (Nat.lt_succ_self n))).1
        rw [this, ih (fun j hj => hk j (by omega))]; norm_cast
    have tapeInv : ∀ k, (branch k).tape = (M.initConfig w).tape := by
      intro k; induction k with
      | zero => exact congr_arg Config.tape hValid.1
      | succ n ih =>
        by_cases h : M.isHaltConfig (branch n)
        · rw [congr_arg Config.tape ((hValid.2 n).2 h)]; exact ih
        · rw [(trans_right_wb n h).2]; exact ih
    have halt_stays : ∀ k, M.isHaltConfig (branch k) →
      M.isHaltConfig (branch (k + 1)) := by
      intro k h
      have heq := (hValid.2 k).2 h
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig] at h ⊢
      rwa [show (branch (k + 1)).state = (branch k).state from congr_arg Config.state heq]
    have halt_persists : ∀ k j, M.isHaltConfig (branch k) → k ≤ j →
      M.isHaltConfig (branch j) := by
      intro k j hH hkj
      have : ∀ m, M.isHaltConfig (branch (k + m)) := by
        intro m; induction m with
        | zero => simpa
        | succ n ih => rw [show k + (n + 1) = (k + n) + 1 from by omega]; exact halt_stays _ ih
      have hj := this (j - k); rw [show k + (j - k) = j from by omega] at hj; exact hj
    have machine_halts : ∃ h ≤ w.length + 1, M.isHaltConfig (branch h) := by
      by_cases hEarly : ∃ k ≤ w.length, M.isHaltConfig (branch k)
      · obtain ⟨k, hk, hH⟩ := hEarly; exact ⟨k, by omega, hH⟩
      · push_neg at hEarly
        have hRead : (branch w.length).tape (branch w.length).headPos = default := by
          rw [tapeInv, headPos_eq w.length (fun j hj => hEarly j (by omega))]
          simp [NTM.initConfig, M_def, tqbfNTM,
            show ¬((0 : ℤ) ≤ ↑w.length ∧ (↑w.length : ℤ) < ↑w.length) from by omega]
        have hNH := hEarly w.length (le_refl _)
        have hStep := (hValid.2 w.length).1 hNH
        obtain ⟨_, q', b, d, hMem, hSt, _, _⟩ := hStep
        have : ∃ buf, (branch w.length).state = ((⟨0, by omega⟩ : Fin 3), buf) := by
          revert hMem
          generalize hst : (branch w.length).state = st
          intro hMem
          match st with
          | (⟨0, h0⟩, buf) => exact ⟨buf, by rw [← hst]⟩
          | (⟨1, _⟩, _) => simp [M_def, tqbfNTM] at hMem
          | (⟨2, _⟩, _) => simp [M_def, tqbfNTM] at hMem
        obtain ⟨buf, hBuf⟩ := this
        have hMem' := hMem
        rw [hBuf, hRead] at hMem'
        simp only [M_def, tqbfNTM, ↓reduceIte] at hMem'
        refine ⟨w.length + 1, le_refl _, ?_⟩
        simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, tqbfNTM]
        split_ifs at hMem' with hR
        · have heq := Set.eq_of_mem_singleton hMem'
          have hq : q' = (⟨1, tqbfNTM._proof_2⟩, []) := congr_arg (·.1) heq
          left; rw [hSt, hq]
        · have heq := Set.eq_of_mem_singleton hMem'
          have hq : q' = (⟨2, tqbfNTM._proof_3⟩, []) := congr_arg (·.1) heq
          right; rw [hSt, hq]
    obtain ⟨h, h_le, hHalt_h⟩ := machine_halts
    have ⟨h₀, hH₀, hMin⟩ : ∃ h₀, M.isHaltConfig (branch h₀) ∧
      ∀ j < h₀, ¬M.isHaltConfig (branch j) := by
      have hEx : ∃ n, M.isHaltConfig (branch n) := ⟨h, hHalt_h⟩
      haveI : DecidablePred (fun j => M.isHaltConfig (branch j)) :=
        fun j => Classical.dec _
      exact ⟨Nat.find hEx, Nat.find_spec hEx, fun j hj => Nat.find_min hEx hj⟩
    have h₀_le : h₀ ≤ w.length + 1 := by
      by_contra hc; push_neg at hc
      exact (hMin h (by omega)) hHalt_h
    constructor
    · exact ⟨h₀, hH₀⟩
    · intro k hHalt_k
      have hpos_j : ∀ j, (branch j).headPos = ↑(min j h₀) := by
        intro j
        by_cases hj : j ≤ h₀
        · simp [Nat.min_eq_left hj]
          exact headPos_eq j (fun i hi => hMin i (by omega))
        · push_neg at hj
          simp [show h₀ ≤ j from by omega, Nat.min_eq_right (by omega : h₀ ≤ j)]
          have hpos_h₀ : (branch h₀).headPos = ↑h₀ := headPos_eq h₀ hMin
          suffices ∀ m, h₀ ≤ m → (branch m).headPos = ↑h₀ from this j (by omega)
          intro m hm; induction m with
          | zero =>
            have h0eq : h₀ = 0 := by omega
            rw [h0eq]; simp [congr_arg Config.headPos hValid.1, NTM.initConfig]
          | succ n ih =>
            by_cases hn : h₀ ≤ n
            · rw [congr_arg Config.headPos ((hValid.2 n).2 (halt_persists h₀ n hH₀ hn))]
              exact ih hn
            · have : n + 1 = h₀ := by omega
              rw [this]; exact hpos_h₀
      simp only [NTMBranchSpaceUsed]
      calc Finset.card ((Finset.range (k + 1)).image (fun j => (branch j).headPos))
        ≤ Finset.card ((Finset.range (h₀ + 1)).image (fun i : ℕ => (↑i : ℤ))) := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_image, Finset.mem_range] at hx ⊢
          obtain ⟨j, _, rfl⟩ := hx
          rw [hpos_j j]
          exact ⟨min j h₀, by omega, by push_cast; rfl⟩
        _ ≤ h₀ + 1 := by
          rw [Finset.card_image_of_injective _ (fun a b hab => by exact_mod_cast hab)]
          simp [Finset.card_range]
        _ ≤ w.length + 2 := by omega

end SpaceComplexity

namespace SpaceComplexity

/--
[tqbfBaseBody_vars](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma tqbfBaseBody_vars
  {n : ℕ} :
-- imply
  (tqbfBaseBody n).vars = Finset.range n := by
-- proof
  induction n with
  | zero => simp [tqbfBaseBody, NPCompleteness.BoolFormula.vars, Finset.range_zero]
  | succ k ih =>
    simp only [tqbfBaseBody, NPCompleteness.BoolFormula.vars, ih]
    ext x
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_range]
    omega

end SpaceComplexity

namespace SpaceComplexity

/--
[freeVars_quantifyHalving](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma freeVars_quantifyHalving
  {q : QBF}
  {configSize : ℕ}
  {n : ℕ} :
-- imply
  (quantifyHalving q configSize n).freeVars = q.freeVars \ Finset.range n := by
-- proof
  induction n with
  | zero => simp [quantifyHalving, Finset.range_zero]
  | succ k ih =>
    simp only [quantifyHalving]
    split
    ·
      simp only [QBF.freeVars, ih, Finset.erase_eq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_range]
      constructor
      · intro ⟨⟨hx1, hx2⟩, hne⟩; exact ⟨hx1, by omega⟩
      · intro ⟨hx1, hx2⟩; exact ⟨⟨hx1, by omega⟩, by omega⟩
    ·
      simp only [QBF.freeVars, ih, Finset.erase_eq]
      ext x
      simp only [Finset.mem_sdiff, Finset.mem_singleton, Finset.mem_range]
      constructor
      · intro ⟨⟨hx1, hx2⟩, hne⟩; exact ⟨hx1, by omega⟩
      · intro ⟨hx1, hx2⟩; exact ⟨⟨hx1, by omega⟩, by omega⟩

end SpaceComplexity

namespace SpaceComplexity

/--
[buildTQBFFormula_isFullyQuantified](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma buildTQBFFormula_isFullyQuantified
  {Q : Type}
  [DecidableEq Q]
  {Γ : Type}
  {M : TM Q Γ}
  {w : List Γ}
  {spacebound : ℕ} :
-- imply
  (buildTQBFFormula M w spacebound).IsFullyQuantified := by
-- proof
  unfold buildTQBFFormula QBF.IsFullyQuantified
  simp only []
  rw [freeVars_quantifyHalving]
  simp [QBF.freeVars, tqbfBaseBody_vars]

end SpaceComplexity

namespace SpaceComplexity

/--
[ggNTM_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/SpaceComplexity.lean)
-/
@[path]
lemma ggNTM_language
  {Γ : Type}
  [Inhabited Γ]
  [DecidableEq Γ]
  [Fintype Γ]
  {enc : GGEncoding Γ} :
-- imply
  (ggNTM enc).language = ggLanguage enc := by
-- proof
  set M := ggNTM enc with M_def
  ext w
  simp only [NTM.language, Set.mem_setOf_eq, ggLanguage, Set.mem_setOf_eq]
  constructor
  ·
    intro ⟨hAlpha, branch, k, hValid, hAccept⟩
    have hNonBlank : ∀ s ∈ w, s ≠ (default : Γ) := fun s hs => hAlpha s hs
    have scanInv : ∀ i : ℕ, i ≤ w.length →
      (branch i).state = ((⟨0, by omega⟩ : Fin 3), w.take i) ∧
      (branch i).headPos = (i : ℤ) ∧
      (branch i).tape = (M.initConfig w).tape := by
      intro i hi
      induction i with
      | zero =>
        exact ⟨congr_arg Config.state hValid.1, congr_arg Config.headPos hValid.1,
          congr_arg Config.tape hValid.1⟩
      | succ n ih =>
        have hn : n < w.length := Nat.lt_of_succ_le hi
        obtain ⟨hS, hH, hT⟩ := ih (Nat.le_of_lt hn)
        have hNotHalt : ¬M.isHaltConfig (branch n) := by
          simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM]
          rw [hS]; intro h; rcases h with h | h <;> simp [GGState] at h
        have hStep := (hValid.2 n).1 hNotHalt
        have hRead : (branch n).tape (branch n).headPos = w.get ⟨n, hn⟩ := by
          rw [hT, hH]; simp [NTM.initConfig, M_def, ggNTM, show (0 : ℤ) ≤ (n : ℤ) from by omega,
            show (n : ℤ) < (w.length : ℤ) from by omega]
        have hSymNB : w.get ⟨n, hn⟩ ≠ (default : Γ) :=
          hNonBlank _ (List.get_mem w ⟨n, hn⟩)
        obtain ⟨_, q', b, d, hMem, hSt, hHd, hTp⟩ := hStep
        have hTrEq : (q', b, d) = ((⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]),
          w.get ⟨n, hn⟩, Direction.R) := by
          have h := hMem; rw [hS, hRead] at h
          simp only [M_def, ggNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff] at h
          exact h
        obtain ⟨hq', hb, hd⟩ : q' = (⟨0, by omega⟩, w.take n ++ [w.get ⟨n, hn⟩]) ∧
          b = w.get ⟨n, hn⟩ ∧ d = Direction.R :=
          ⟨congr_arg Prod.fst hTrEq, congr_arg (fun x => x.2.1) hTrEq,
            congr_arg (fun x => x.2.2) hTrEq⟩
        refine ⟨?_, ?_, ?_⟩
        · rw [hSt, hq', List.take_succ_eq_append_getElem hn]; simp [List.get_eq_getElem]
        · rw [hHd, hd, hH]; norm_cast
        · rw [hTp, hT, hH, hb, ← hRead, hT, hH]; exact Function.update_eq_self _ _
    obtain ⟨hS_end, hH_end, hT_end⟩ := scanInv w.length le_rfl
    rw [List.take_length] at hS_end
    have hNotHalt_end : ¬M.isHaltConfig (branch w.length) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM]
      rw [hS_end]; intro h; rcases h with h | h <;> simp [GGState] at h
    have hReadBlank : (branch w.length).tape (branch w.length).headPos = (default : Γ) := by
      rw [hT_end, hH_end]; simp [NTM.initConfig, M_def, ggNTM]
    have hStepEnd := (hValid.2 w.length).1 hNotHalt_end
    obtain ⟨_, q'', b'', d'', hMem'', hSt'', _, _⟩ := hStepEnd
    have hTransIn : (q'', b'', d'') ∈ M.δ ((⟨0, by omega⟩ : Fin 3), w) (default : Γ) := by
      have h := hMem''; rwa [hS_end, hReadBlank] at h
    have hNotAccBefore : ∀ i, i ≤ w.length → (branch i).state ≠ M.qAccept := by
      intro i hi hEq; have ⟨hSi, _, _⟩ := scanInv i hi
      rw [hSi] at hEq; simp [M_def, ggNTM, GGState] at hEq
    have hk_gt : k > w.length := by
      by_contra h; push_neg at h; exact hNotAccBefore k h hAccept
    have hHalt_next : M.isHaltConfig (branch (w.length + 1)) := by
      simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM, hSt'']
      simp only [M_def, ggNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      split_ifs at hTransIn <;> (obtain ⟨rfl, -, -⟩ := hTransIn; simp [GGState])
    have hConst : ∀ j, j ≥ w.length + 1 → branch j = branch (w.length + 1) := by
      intro j hj; induction j with
      | zero => omega
      | succ m ihm =>
        by_cases hm : m ≥ w.length + 1
        · have heq := ihm hm
          exact ((hValid.2 m).2 (heq ▸ hHalt_next)).symm ▸ heq
        · push_neg at hm; congr 1; omega
    have hAccNext : (branch (w.length + 1)).state = M.qAccept := by
      have := hConst k (by omega); rw [← this]; exact hAccept
    have hq''_acc : q'' = ((⟨1, by omega⟩ : Fin 3), ([] : List Γ)) := by
      rw [hSt''] at hAccNext; exact hAccNext
    have hResultTrue : (match enc.decode w with
      | some p => @decide (@GeographyGame.GG enc.V enc.decEqV p.1 p.2) (Classical.dec _)
      | none => false) = true := by
      by_contra hFalse; push_neg at hFalse; simp only [Bool.not_eq_true] at hFalse
      simp only [M_def, ggNTM, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      simp only [hFalse, ↓reduceIte, Set.mem_singleton_iff] at hTransIn
      obtain ⟨rfl, -, -⟩ := hTransIn
      simp [GGState] at hq''_acc
    cases hDec : enc.decode w with
    | none => simp [hDec] at hResultTrue
    | some p =>
      simp [hDec] at hResultTrue
      exact ⟨p, enc.encode_decode w p hDec, hResultTrue⟩
  ·
    intro ⟨p, hEncode, hGG⟩
    refine ⟨?_, ?_⟩
    · intro s hs
      simp only [M_def, ggNTM, NTM.inputAlpha, Set.mem_setOf_eq]
      exact fun heq => enc.blank_free p (hEncode ▸ heq ▸ hs)
    · refine ⟨fun n =>
      if n ≤ w.length then
        ⟨((⟨0, by omega⟩ : Fin 3), w.take n), (n : ℤ), (M.initConfig w).tape⟩
      else
        ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), ((w.length : ℤ) + 1),
          Function.update (M.initConfig w).tape (↑w.length) default⟩,
      w.length + 1, ?_, ?_⟩
      · constructor
        · simp [NTM.initConfig, M_def, ggNTM]
        · intro n; constructor
          · intro hNotHalt
            simp only [NTM.step]; refine ⟨hNotHalt, ?_⟩
            by_cases hn_le : n ≤ w.length
            · by_cases hn_lt : n < w.length
              · simp only [hn_le, ↓reduceIte]
                have hRead : (M.initConfig w).tape (↑n) = w.get ⟨n, hn_lt⟩ := by
                  simp [NTM.initConfig, M_def, ggNTM,
                    show (0 : ℤ) ≤ (n : ℤ) from by omega,
                    show (n : ℤ) < (w.length : ℤ) from by omega]
                have hSymNB : w.get ⟨n, hn_lt⟩ ≠ (default : Γ) := by
                  exact fun h => enc.blank_free p (hEncode ▸ h ▸ List.get_mem w ⟨n, hn_lt⟩)
                refine ⟨((⟨0, by omega⟩ : Fin 3), w.take n ++ [w.get ⟨n, hn_lt⟩]),
                  w.get ⟨n, hn_lt⟩, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, _⟩, w.take n)) ((M.initConfig w).tape ↑n)
                  rw [hRead]
                  simp only [M_def, ggNTM, hSymNB, ↓reduceIte, Set.mem_singleton_iff]
                  simp only [List.get_eq_getElem]
                  rfl
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [List.take_succ_eq_append_getElem hn_lt]; simp [List.get_eq_getElem]
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]; norm_cast
                · simp only [show n + 1 ≤ w.length from hn_lt, ↓reduceIte]
                  rw [← hRead]; exact (Function.update_eq_self ((↑n : ℤ)) _).symm
              · have hn_eq : n = w.length := Nat.le_antisymm hn_le (by omega)
                subst hn_eq
                simp only [le_refl, ↓reduceIte, List.take_length]
                have hReadBl : (M.initConfig w).tape (↑w.length : ℤ) = (default : Γ) := by
                  simp [NTM.initConfig, M_def, ggNTM]
                have hDecW : enc.decode w = some p := by rw [← hEncode]; exact enc.decode_encode p
                have hResult : (match enc.decode w with
                  | some p' => @decide (@GeographyGame.GG enc.V enc.decEqV p'.1 p'.2) (Classical.dec _)
                  | none => false) = true := by
                  rw [hDecW]; simp only [decide_eq_true_eq]; exact hGG
                refine ⟨((⟨1, by omega⟩ : Fin 3), ([] : List Γ)), default, Direction.R, ?_, ?_, ?_, ?_⟩
                · show _ ∈ M.δ ((⟨0, (by omega : (0 : Fin 3).val < 3)⟩, w)) ((M.initConfig w).tape ↑w.length)
                  rw [hReadBl]
                  simp only [M_def, ggNTM, ↓reduceIte, hResult, Set.mem_singleton_iff]
                  rfl
                · simp [show ¬(w.length + 1 ≤ w.length) from by omega]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false, Direction]
                · simp only [show ¬(w.length + 1 ≤ w.length) from by omega, ite_false]
            · exfalso; apply hNotHalt
              simp only [NTM.isHaltConfig, NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM,
                show ¬(n ≤ w.length) from hn_le, ↓reduceIte]
              left; trivial
          · intro hHalt
            by_cases hn_le : n ≤ w.length
            · exfalso; apply hHalt.elim <;> intro h <;>
              simp [NTM.isAcceptConfig, NTM.isRejectConfig, M_def, ggNTM, hn_le, GGState] at h
            · simp [show ¬(n ≤ w.length) from hn_le, show ¬(n + 1 ≤ w.length) from by omega]
      · simp only [NTM.isAcceptConfig, M_def, ggNTM, show ¬(w.length + 1 ≤ w.length) from by omega,
        ↓reduceIte]

end SpaceComplexity


-- created on 2026-10-23
