import Mathlib
import sympy.Basic
import Def.v1.Atlas.TheoryOfComputation.code.TuringMachines.Part4
open TuringMachine
open Direction


namespace TuringMachine

/--
[TM.step_of_accept](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.step_of_accept
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
-- given
  (h : M.isAcceptConfig c) :
-- imply
  M.step c = c := by
-- proof
  simp only [TM.step, TM.isAcceptConfig] at *
  simp [h]

end TuringMachine

namespace TuringMachine

/--
[TM.step_of_reject](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.step_of_reject
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
-- given
  (h : M.isRejectConfig c) :
-- imply
  M.step c = c := by
-- proof
  simp only [TM.step, TM.isRejectConfig] at *
  simp [h]

end TuringMachine

namespace TuringMachine

/--
[TM.step_of_halt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.step_of_halt
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
-- given
  (h : M.isHaltConfig c) :
-- imply
  M.step c = c := by
-- proof
  obtain h | h := h
  · exact M.step_of_accept c h
  · exact M.step_of_reject c h

end TuringMachine

namespace TuringMachine

/--
[TM.accepts_stable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.accepts_stable
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {n : ℕ}
-- given
  (h : M.isAcceptConfig c) :
-- imply
  M.isAcceptConfig (M.run c n) := by
-- proof
  induction n with
  | zero => exact h
  | succ n ih =>
    simp only [TM.run]
    rwa [M.step_of_accept _ ih]

end TuringMachine

namespace TuringMachine

/--
[TM.run_of_isHaltConfig](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.run_of_isHaltConfig
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {n : ℕ}
-- given
  (h : M.isHaltConfig c) :
-- imply
  M.run c n = c := by
-- proof
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [TM.run]
    rw [ih]
    exact M.step_of_halt c h

end TuringMachine

namespace TuringMachine

/--
[TM.run_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.run_zero
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ} :
-- imply
  M.run c 0 = c :=
-- proof
  rfl

end TuringMachine

namespace TuringMachine

/--
[TM.run_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma TM.run_succ
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {M : TM Q Γ}
  {c : Config Q Γ}
  {n : ℕ} :
-- imply
  M.run c (n + 1) = M.step (M.run c n) :=
-- proof
  rfl

end TuringMachine

namespace TuringMachine

/--
[countingTM_step_state](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma countingTM_step_state
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {Γ : Type}
  {blank : Γ}
  {inputAlpha : Set Γ}
  {c : Config ℕ Γ}
-- given
  (h : blank ∉ inputAlpha)
  (hc : c.state ≥ 2) :
-- imply
  ((countingTM blank inputAlpha h).step c).state = c.state + 1 := by
-- proof
  simp only [TM.step, countingTM]
  have h1 : ¬(c.state = 0 ∨ c.state = 1) := by omega
  simp [h1]

end TuringMachine

namespace TuringMachine

/--
[countingTM_run_state](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma countingTM_run_state
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {Γ : Type}
  {blank : Γ}
  {inputAlpha : Set Γ}
  {c : Config ℕ Γ}
  {n : ℕ}
-- given
  (h : blank ∉ inputAlpha)
  (hc : c.state = 2) :
-- imply
  ((countingTM blank inputAlpha h).run c n).state = 2 + n := by
-- proof
  induction n with
  | zero => simp [TM.run, hc]
  | succ n ih =>
    simp only [TM.run]
    rw [countingTM_step_state]
    · omega
    · omega

end TuringMachine

namespace TuringMachine

/--
[isTuringEnumerable_of_isTuringRecognizable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/TuringMachines.lean)
-/
@[path]
lemma isTuringEnumerable_of_isTuringRecognizable
  {Q : Type}
  {Γ : Type}
  [DecidableEq Q]
  {Γ : Type}
  {A : Set (List Γ)}
-- given
  (h : IsTuringRecognizable A) :
-- imply
  IsTuringEnumerable A := by
-- proof
  obtain ⟨Q_M, hDecEq, M, hLang⟩ := h
  letI : DecidableEq Q_M := hDecEq
  let cTM := countingTM M.blank M.inputAlpha M.blank_not_in_inputAlpha
  let E : TuringEnumerator ℕ Γ := {
    toTM := cTM
    prints := fun c => {w | M.isAcceptConfig (M.runOnInput w (c.state - 2))}
  }
  refine ⟨ℕ, inferInstance, E, ?_⟩
  subst hLang
  ext w
  simp only [TuringEnumerator.language, Set.mem_setOf_eq, TM.language, TM.accepts]
  constructor
  · rintro ⟨n, hw⟩
    have hstate : (E.run n).state = 2 + n := by
      simp only [TuringEnumerator.run, E, cTM]
      apply countingTM_run_state
      simp [TuringEnumerator.initConfig, countingTM]
    change M.isAcceptConfig (M.runOnInput w ((E.run n).state - 2)) at hw
    rw [hstate] at hw
    simp only [Nat.add_sub_cancel_left] at hw
    exact ⟨n, hw⟩
  · rintro ⟨n, hw⟩
    refine ⟨n, ?_⟩
    change M.isAcceptConfig (M.runOnInput w ((E.run n).state - 2))
    have hstate : (E.run n).state = 2 + n := by
      simp only [TuringEnumerator.run, E, cTM]
      apply countingTM_run_state
      simp [TuringEnumerator.initConfig, countingTM]
    rw [hstate]
    simp only [Nat.add_sub_cancel_left]
    exact hw

end TuringMachine


-- created on 2026-10-23
