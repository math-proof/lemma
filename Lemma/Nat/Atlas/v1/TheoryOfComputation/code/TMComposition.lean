import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.TMComposition
open TuringMachine


namespace TuringMachine

/--
[TM.run_add'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma TM.run_add'
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {m n : ℕ} :
-- imply
  M.run c (m + n) = M.run (M.run c m) n := by
-- proof
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show m + (n + 1) = (m + n) + 1 from by omega]
    simp only [TM.run_succ, ih]

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_phase1_run](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_phase1_run
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {c : Config Q₁ Γ}
  {n : ℕ}
-- given
  (hNotHalt : ∀ k, k < n → ¬M₁.isHaltConfig (M₁.run c k)) :
-- imply
  (TM.sequentialCompose M₁ M₂).run ⟨.inl (.inl c.state), c.headPos, c.tape⟩ n = ⟨.inl (.inl (M₁.run c n).state), (M₁.run c n).headPos, (M₁.run c n).tape⟩ := by
-- proof
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    have hk : ∀ k, k < n → ¬M₁.isHaltConfig (M₁.run c k) :=
      fun k hk => hNotHalt k (Nat.lt_succ_of_lt hk)
    rw [TM.run, ih hk, TM.run]
    have hNotHaltN := hNotHalt n (Nat.lt_succ_of_le le_rfl)
    simp only [TM.step, TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig] at hNotHaltN ⊢
    push Not at hNotHaltN
    simp only [TM.sequentialCompose, hNotHaltN, or_self, ite_false, reduceCtorEq]

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_phase2_run](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_phase2_run
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {c : Config Q₂ Γ}
  {n : ℕ}
-- given
  (hNotHalt : ∀ k, k < n → ¬M₂.isHaltConfig (M₂.run c k)) :
-- imply
  (TM.sequentialCompose M₁ M₂).run ⟨.inl (.inr c.state), c.headPos, c.tape⟩ n = ⟨.inl (.inr (M₂.run c n).state), (M₂.run c n).headPos, (M₂.run c n).tape⟩ := by
-- proof
  induction n with
  | zero => simp [TM.run]
  | succ n ih =>
    have hk : ∀ k, k < n → ¬M₂.isHaltConfig (M₂.run c k) :=
      fun k hk => hNotHalt k (Nat.lt_succ_of_lt hk)
    rw [TM.run, ih hk, TM.run]
    have hNotHaltN := hNotHalt n (Nat.lt_succ_of_le le_rfl)
    simp only [TM.step, TM.isHaltConfig, TM.isAcceptConfig, TM.isRejectConfig] at hNotHaltN ⊢
    push Not at hNotHaltN
    simp only [TM.sequentialCompose, hNotHaltN.1, hNotHaltN.2, ite_false, reduceCtorEq, false_or]

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_transition_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_transition_step
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {q₁ : Q₁}
  {tape : Tape Γ}
-- given
  (headPos : ℤ)
  (hHalt : q₁ = M₁.qAccept ∨ q₁ = M₁.qReject) :
-- imply
  (TM.sequentialCompose M₁ M₂).step ⟨.inl (.inl q₁), headPos, tape⟩ = ⟨.inl (.inr M₂.q₀), headPos + 1, tape⟩ := by
-- proof
  simp only [TM.step, TM.sequentialCompose]
  simp [hHalt]

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_phase1_from_init](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_phase1_from_init
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {w : List Γ}
  {n₁ : ℕ}
-- given
  (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k)) :
-- imply
  let M₃ := TM.sequentialCompose M₁ M₂ M₃.run (M₃.initConfig w) n₁ = ⟨.inl (.inl (M₁.runOnInput w n₁).state), (M₁.runOnInput w n₁).headPos, (M₁.runOnInput w n₁).tape⟩ := by
-- proof
  show (TM.sequentialCompose M₁ M₂).run
    ⟨.inl (.inl M₁.q₀), 0, (M₁.initConfig w).tape⟩ n₁ = _
  conv_lhs =>
    rw [show (⟨Sum.inl (Sum.inl M₁.q₀), (0 : ℤ), (M₁.initConfig w).tape⟩ :
      Config ((Q₁ ⊕ Q₂) ⊕ Fin 2) Γ) =
      ⟨.inl (.inl (M₁.initConfig w).state), (M₁.initConfig w).headPos,
        (M₁.initConfig w).tape⟩ from by simp [TM.initConfig]]
  exact sequentialCompose_phase1_run M₁ M₂ (M₁.initConfig w) n₁ hNotHalt₁

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_accepts_of_phases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_accepts_of_phases
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {w : List Γ}
  {n₁ : ℕ}
  {n₂ : ℕ}
-- given
  (hHalt₁ : M₁.isHaltConfig (M₁.runOnInput w n₁))
  (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k))
  (hAccept₂ : M₂.isAcceptConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) n₂))
  (hNotHalt₂ : ∀ k, k < n₂ → ¬M₂.isHaltConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) k)) :
-- imply
  (TM.sequentialCompose M₁ M₂).accepts w := by
-- proof
  let M₃ := TM.sequentialCompose M₁ M₂
  let c₂ := phase2InitConfig M₁ M₂ w n₁
  refine ⟨n₁ + 1 + n₂ + 1, ?_⟩
  have h1 := sequentialCompose_phase1_from_init M₁ M₂ w n₁ hNotHalt₁
  have h2 : M₃.run (M₃.initConfig w) (n₁ + 1) =
    ⟨.inl (.inr M₂.q₀), (M₁.runOnInput w n₁).headPos + 1,
      (M₁.runOnInput w n₁).tape⟩ := by
    rw [TM.run_succ, h1]
    exact sequentialCompose_transition_step M₁ M₂ _ _ _
      (by rcases hHalt₁ with h | h <;> [left; right] <;> exact h)
  have h3 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂) =
    ⟨.inl (.inr (M₂.run c₂ n₂).state),
      (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_add', h2]
    exact sequentialCompose_phase2_run M₁ M₂ c₂ n₂ hNotHalt₂
  have hAcc_state : (M₂.run c₂ n₂).state = M₂.qAccept := hAccept₂
  have h4 : M₃.step ⟨.inl (.inr (M₂.run c₂ n₂).state),
    (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ =
    ⟨.inr ⟨0, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
      (M₂.run c₂ n₂).tape⟩ := by
    simp only [hAcc_state]
    show (TM.sequentialCompose M₁ M₂).step
      ⟨.inl (.inr M₂.qAccept), (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ = _
    simp only [TM.step, TM.sequentialCompose]
    simp
  have h5 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂ + 1) =
    ⟨.inr ⟨0, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
      (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_succ, h3, h4]
  show M₃.isAcceptConfig (M₃.runOnInput w (n₁ + 1 + n₂ + 1))
  show (M₃.runOnInput w (n₁ + 1 + n₂ + 1)).state = M₃.qAccept
  simp only [TM.runOnInput, h5]
  rfl

end TuringMachine

namespace TuringMachine

/--
[sequentialCompose_rejects_of_phases](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TMComposition.lean)
-/
@[path]
lemma sequentialCompose_rejects_of_phases
  {Q₁ Q₂ Γ : Type}
  [DecidableEq Q₁]
  [DecidableEq Q₂]
  {M₁ : TM Q₁ Γ}
  {M₂ : TM Q₂ Γ}
  {w : List Γ}
  {n₁ : ℕ}
  {n₂ : ℕ}
-- given
  (hHalt₁ : M₁.isHaltConfig (M₁.runOnInput w n₁))
  (hNotHalt₁ : ∀ k, k < n₁ → ¬M₁.isHaltConfig (M₁.runOnInput w k))
  (hReject₂ : M₂.isRejectConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) n₂))
  (hNotHalt₂ : ∀ k, k < n₂ → ¬M₂.isHaltConfig (M₂.run (phase2InitConfig M₁ M₂ w n₁) k)) :
-- imply
  (TM.sequentialCompose M₁ M₂).rejects w := by
-- proof
  let M₃ := TM.sequentialCompose M₁ M₂
  let c₂ := phase2InitConfig M₁ M₂ w n₁
  refine ⟨n₁ + 1 + n₂ + 1, ?_⟩
  have h1 := sequentialCompose_phase1_from_init M₁ M₂ w n₁ hNotHalt₁
  have h2 : M₃.run (M₃.initConfig w) (n₁ + 1) =
    ⟨.inl (.inr M₂.q₀), (M₁.runOnInput w n₁).headPos + 1,
      (M₁.runOnInput w n₁).tape⟩ := by
    rw [TM.run_succ, h1]
    exact sequentialCompose_transition_step M₁ M₂ _ _ _
      (by rcases hHalt₁ with h | h <;> [left; right] <;> exact h)
  have h3 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂) =
    ⟨.inl (.inr (M₂.run c₂ n₂).state),
      (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_add', h2]
    exact sequentialCompose_phase2_run M₁ M₂ c₂ n₂ hNotHalt₂
  have hRej_state : (M₂.run c₂ n₂).state = M₂.qReject := hReject₂
  have h4 : M₃.step ⟨.inl (.inr (M₂.run c₂ n₂).state),
    (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ =
    ⟨.inr ⟨1, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
      (M₂.run c₂ n₂).tape⟩ := by
    simp only [hRej_state]
    show (TM.sequentialCompose M₁ M₂).step
      ⟨.inl (.inr M₂.qReject), (M₂.run c₂ n₂).headPos, (M₂.run c₂ n₂).tape⟩ = _
    simp only [TM.step, TM.sequentialCompose]
    simp [M₂.qReject_ne_qAccept]
  have h5 : M₃.run (M₃.initConfig w) (n₁ + 1 + n₂ + 1) =
    ⟨.inr ⟨1, by omega⟩, (M₂.run c₂ n₂).headPos + 1,
      (M₂.run c₂ n₂).tape⟩ := by
    rw [TM.run_succ, h3, h4]
  show M₃.isRejectConfig (M₃.runOnInput w (n₁ + 1 + n₂ + 1))
  show (M₃.runOnInput w (n₁ + 1 + n₂ + 1)).state = M₃.qReject
  simp only [TM.runOnInput, h5]
  rfl

end TuringMachine


-- created on 2026-10-23
