import Mathlib
import sympy.Basic
import Inductive.v1.Atlas.TheoryOfComputation.code.CFGtoPDA.Part2
open CFGtoPDA
open ContextFreeGrammar ContextFreeRule


namespace CFGtoPDA

/--
[toPDA_push_list](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_push_list
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {L : List (Symbol T g.NT)}
  {input : List T}
  {stack : List (Option (Symbol T g.NT))} :
-- imply
  (toPDA g).Reaches (QState.pushing L, input, stack) (QState.loop, input, L.reverse.map some ++ stack) := by
-- proof
  induction L generalizing stack with
  | nil =>
    simp only [List.reverse_nil, List.map_nil, List.nil_append]
    apply Relation.ReflTransGen.single
    have h := PDA.Step.mk (M := toPDA g) (QState.pushing []) QState.loop
      (none : Option T) (none : Option (Option (Symbol T g.NT))) none input stack
      (by simp [toPDA])
    simpa [Option.toList] using h
  | cons s rest ih =>
    apply Relation.ReflTransGen.head
    · have h := PDA.Step.mk (M := toPDA g) (QState.pushing (s :: rest)) (QState.pushing rest)
      (none : Option T) (none : Option (Option (Symbol T g.NT))) (some (some s)) input stack
      (by simp [toPDA])
      simpa [Option.toList] using h
    · simp only [List.reverse_cons, List.map_append, List.map_cons, List.map_nil,
      List.append_assoc, List.singleton_append] at *
      exact ih _
set_option maxRecDepth 1024 in

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_pop_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_pop_terminal
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {t : T}
  {input : List T}
  {stack : List (Option (Symbol T g.NT))} :
-- imply
  (toPDA g).Reaches (QState.loop, t :: input, some (Symbol.terminal t) :: stack) (QState.loop, input, stack) := by
-- proof
  apply Relation.ReflTransGen.single
  have h := PDA.Step.mk (M := toPDA g) QState.loop QState.loop
    (some t) (some (some (Symbol.terminal t))) none input stack (by simp [toPDA])
  simpa [Option.toList] using h
set_option maxRecDepth 1024 in

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_apply_rule](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_apply_rule
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {r : ContextFreeRule T g.NT}
  {input : List T}
  {stack : List (Option (Symbol T g.NT))}
-- given
  (hr : r ∈ g.rules) :
-- imply
  (toPDA g).Reaches (QState.loop, input, some (Symbol.nonterminal r.input) :: stack) (QState.loop, input, r.output.map some ++ stack) := by
-- proof
  apply Relation.ReflTransGen.head
  · have h := PDA.Step.mk (M := toPDA g) QState.loop (QState.pushing r.output.reverse)
    (none : Option T) (some (some (Symbol.nonterminal r.input))) none input stack
    (show _ ∈ _ from ⟨r, hr, rfl, rfl⟩)
    simpa [Option.toList] using h
  · have h := toPDA_push_list r.output.reverse input stack
    simp only [List.reverse_reverse] at h
    convert h using 2

end CFGtoPDA

namespace CFGtoPDA

/--
[derivesIn'_zero_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derivesIn'_zero_eq
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {γ δ : List (Symbol T g.NT)}
-- given
  (h : DerivesIn' g 0 γ δ) :
-- imply
  γ = δ := by
-- proof
cases h; rfl

end CFGtoPDA

namespace CFGtoPDA

/--
[derivesIn'_snoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derivesIn'_snoc
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {n : ℕ}
  {γ mid δ : List (Symbol T g.NT)}
-- given
  (h : DerivesIn' g n γ mid)
  (hp : g.Produces mid δ) :
-- imply
  DerivesIn' g (n + 1) γ δ := by
-- proof
  induction h with
  | refl => exact DerivesIn'.step hp (DerivesIn'.refl _)
  | step hprod _ ih => exact DerivesIn'.step hprod (ih hp)

end CFGtoPDA

namespace CFGtoPDA

/--
[derives_to_derivesIn'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derives_to_derivesIn'
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {γ δ : List (Symbol T g.NT)}
-- given
  (h : g.Derives γ δ) :
-- imply
  ∃ n, DerivesIn' g n γ δ := by
-- proof
  induction h with
  | refl => exact ⟨0, DerivesIn'.refl _⟩
  | tail _ hprod ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, derivesIn'_snoc hn hprod⟩

end CFGtoPDA

namespace CFGtoPDA

/--
[produces_cons_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma produces_cons_terminal
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {t : T}
  {γ' δ : List (Symbol T g.NT)}
-- given
  (h : g.Produces (Symbol.terminal t :: γ') δ) :
-- imply
  ∃ δ', δ = Symbol.terminal t :: δ' ∧ g.Produces γ' δ' := by
-- proof
  obtain ⟨r, hr_mem, hr_rew⟩ := h
  rw [ContextFreeRule.rewrites_iff] at hr_rew
  obtain ⟨p, q, hpq1, hpq2⟩ := hr_rew
  cases p with
  | nil => simp at hpq1
  | cons x p' =>
    simp at hpq1; obtain ⟨rfl, rfl⟩ := hpq1
    refine ⟨p' ++ r.output ++ q, ?_, ⟨r, hr_mem, ?_⟩⟩
    · simp [hpq2]
    · convert ContextFreeRule.rewrites_of_exists_parts r p' q using 1; simp

end CFGtoPDA

namespace CFGtoPDA

/--
[derivesIn'_cons_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derivesIn'_cons_terminal
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {n : ℕ}
  {t : T}
  {γ' δ : List (Symbol T g.NT)}
-- given
  (h : DerivesIn' g n (Symbol.terminal t :: γ') δ) :
-- imply
  ∃ δ', δ = Symbol.terminal t :: δ' ∧ DerivesIn' g n γ' δ' := by
-- proof
  induction n generalizing γ' δ with
  | zero => cases h with | refl => exact ⟨γ', rfl, DerivesIn'.refl _⟩
  | succ n ih =>
    cases h with
    | step hprod hrest =>
      obtain ⟨v', rfl, hprod'⟩ := produces_cons_terminal hprod
      obtain ⟨δ', rfl, hδ'⟩ := ih hrest
      exact ⟨δ', rfl, DerivesIn'.step hprod' hδ'⟩

end CFGtoPDA

namespace CFGtoPDA

/--
[derivesIn'_nil_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derivesIn'_nil_inv
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {n : ℕ}
  {δ : List (Symbol T g.NT)}
-- given
  (h : DerivesIn' g n ([] : List (Symbol T g.NT)) δ) :
-- imply
  n = 0 ∧ δ = [] := by
-- proof
  cases n with
  | zero => cases h with | refl => exact ⟨rfl, rfl⟩
  | succ n =>
    cases h with | step hprod _ =>
      obtain ⟨r, _, hr_rew⟩ := hprod
      rw [ContextFreeRule.rewrites_iff] at hr_rew
      obtain ⟨p, _, hpq, _⟩ := hr_rew; simp at hpq

end CFGtoPDA

namespace CFGtoPDA

/--
[leftmost_step_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma leftmost_step_n
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {n : ℕ}
  {A : g.NT}
  {γ' target : List (Symbol T g.NT)}
-- given
  (h : DerivesIn' g (n + 1) (Symbol.nonterminal A :: γ') target)
  (h_target : ∀ s ∈ target, ∃ t, s = Symbol.terminal t) :
-- imply
  ∃ r ∈ g.rules, r.input = A ∧ ∃ m, m ≤ n ∧ DerivesIn' g m (r.output ++ γ') target := by
-- proof
  induction n generalizing A γ' target with
  | zero =>
    cases h with | step hprod hrest =>
    have hv_eq := derivesIn'_zero_eq hrest; subst hv_eq
    obtain ⟨r, hr_mem, hr_rew⟩ := hprod
    rw [ContextFreeRule.rewrites_iff] at hr_rew
    obtain ⟨p, q, hu_eq, hv_eq⟩ := hr_rew
    cases p with
    | nil =>
      simp at hu_eq; obtain ⟨hA, hq⟩ := hu_eq; subst hq; subst hA
      exact ⟨r, hr_mem, rfl, 0, le_refl _, by simp at hv_eq; rw [hv_eq]; exact DerivesIn'.refl _⟩
    | cons x p' =>
      simp at hu_eq; obtain ⟨hx, _⟩ := hu_eq; exfalso
      have := h_target x (by rw [hv_eq]; simp)
      rw [← hx] at this; obtain ⟨t, ht⟩ := this; simp at ht
  | succ n' ih =>
    cases h with | step hprod hrest =>
    obtain ⟨r, hr_mem, hr_rew⟩ := hprod
    rw [ContextFreeRule.rewrites_iff] at hr_rew
    obtain ⟨p, q, hu_eq, hv_eq⟩ := hr_rew
    cases p with
    | nil =>
      simp at hu_eq; obtain ⟨hA, hq⟩ := hu_eq; subst hq; subst hA
      exact ⟨r, hr_mem, rfl, n' + 1, by omega, by simp at hv_eq; rw [hv_eq] at hrest; exact hrest⟩
    | cons x p' =>
      simp at hu_eq; obtain ⟨hx, hγ'⟩ := hu_eq
      have hrest' : DerivesIn' g (n' + 1)
        (Symbol.nonterminal A :: (p' ++ r.output ++ q)) target := by
        rw [hv_eq, ← hx] at hrest; simpa using hrest
      obtain ⟨r', hr'_mem, hr'_input, m, hm, hm_deriv⟩ :=
        ih A (p' ++ r.output ++ q) target hrest' h_target
      refine ⟨r', hr'_mem, hr'_input, m + 1, by omega, ?_⟩
      have hprod_γ' : g.Produces γ' (p' ++ r.output ++ q) := by
        rw [hγ']; refine ⟨r, hr_mem, ?_⟩
        convert ContextFreeRule.rewrites_of_exists_parts r p' q using 1; simp
      exact DerivesIn'.step (hprod_γ'.append_left r'.output) hm_deriv

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_simulates](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_simulates
  {T : Type u_pda}
  {g : ContextFreeGrammar T} :
-- imply
  ∀ (n : ℕ) (γ : List (Symbol T g.NT)) (w : List T) (extra : List (Option (Symbol T g.NT))), DerivesIn' g n γ (w.map Symbol.terminal) → (toPDA g).Reaches (QState.loop, w, γ.map some ++ extra) (QState.loop, [], extra) := by
-- proof
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih_n =>
    intro γ
    induction γ with
    | nil =>
      intro w extra h
      have ⟨_, hw⟩ := derivesIn'_nil_inv h
      cases w with
      | nil => simp; exact Relation.ReflTransGen.refl
      | cons _ _ => simp at hw
    | cons s γ' ih_γ =>
      intro w extra h
      match s with
      | Symbol.terminal t =>
        obtain ⟨w', hw_eq, hw'_deriv⟩ := derivesIn'_cons_terminal h
        match w with
        | [] => simp at hw_eq
        | t' :: w'' =>
          simp at hw_eq; obtain ⟨ht, hw'⟩ := hw_eq; subst ht
          rw [← hw'] at hw'_deriv
          simp only [List.map_cons]
          exact (toPDA_pop_terminal t' w'' (γ'.map some ++ extra)).trans
            (ih_γ w'' extra hw'_deriv)
      | Symbol.nonterminal A =>
        match n with
        | 0 =>
          exfalso; have := derivesIn'_zero_eq h
          cases w with | nil => simp at this | cons _ _ => simp at this
        | n' + 1 =>
          have h_target : ∀ s ∈ (w.map (Symbol.terminal (N := g.NT))),
            ∃ t, s = Symbol.terminal t := by simp
          obtain ⟨r, hr_mem, hr_input, m, hm, hm_deriv⟩ :=
            leftmost_step_n n' A γ' (w.map Symbol.terminal) h h_target
          simp only [List.map_cons]
          apply Relation.ReflTransGen.trans
          · subst hr_input
            exact toPDA_apply_rule r hr_mem w (γ'.map some ++ extra)
          · have : (r.output.map some ++ (List.map some γ' ++ extra)) =
            ((r.output ++ γ').map some ++ extra) := by
            simp [List.map_append]
            rw [this]
            exact ih_n m (by omega) (r.output ++ γ') w extra hm_deriv

end CFGtoPDA

namespace CFGtoPDA

/--
[derives_cons_same](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma derives_cons_same
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {s : Symbol T g.NT}
  {γ δ : List (Symbol T g.NT)}
-- given
  (h : g.Derives γ δ) :
-- imply
  g.Derives (s :: γ) (s :: δ) := by
-- proof
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih =>
    exact ih.trans (Relation.ReflTransGen.single (hstep.append_left [s]))
set_option maxRecDepth 2048 in

end CFGtoPDA

namespace CFGtoPDA

/--
[no_step_from_accept](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma no_step_from_accept
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {w' : List T}
  {stk' : List (Option (Symbol T g.NT))}
  {cfg'}
-- given
  (h : (toPDA g).Step (QState.accept, w', stk') cfg') :
-- imply
  False := by
-- proof
  generalize hc : (QState.accept, w', stk') = c at h
  cases h with
  | mk q q' a pop push inp stk'' hmem =>
    simp only [Prod.mk.injEq] at hc
    obtain ⟨hq, _, _⟩ := hc; subst hq
    cases pop with
    | some _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
    | none => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem

end CFGtoPDA

namespace CFGtoPDA

/--
[reaches_from_accept](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma reaches_from_accept
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {w' : List T}
  {stk' : List (Option (Symbol T g.NT))}
  {cfg'}
-- given
  (h : (toPDA g).Reaches (QState.accept, w', stk') cfg') :
-- imply
  cfg' = (QState.accept, w', stk') := by
-- proof
  induction h with
  | refl => rfl
  | tail _ hs ih => subst ih; exact absurd hs no_step_from_accept

end CFGtoPDA

namespace CFGtoPDA

/--
[StepCount.to_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma StepCount.to_reaches
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {M : PDA T σ γ₁}
  {n c1 c2}
-- given
  (h : StepCount M n c1 c2) :
-- imply
  M.Reaches c1 c2 := by
-- proof
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | step hs _ ih => exact Relation.ReflTransGen.head hs ih

end CFGtoPDA

namespace CFGtoPDA

/--
[StepCount.snoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma StepCount.snoc
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {M : PDA T σ γ₁}
  {n : ℕ}
  {c1 c2 c3 : PDA.Config (α := T) (σ := σ) (γ := γ₁)}
-- given
  (h0 : StepCount M n c1 c2)
  (h1 : M.Step c2 c3) :
-- imply
  StepCount M (n + 1) c1 c3 := by
-- proof
  induction h1 with
  | refl => exact StepCount.step h2 (StepCount.refl _)
  | step hs _ ih => rw [Nat.add_right_comm]; exact StepCount.step hs (ih h2)

end CFGtoPDA

namespace CFGtoPDA

/--
[stepCount_of_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma stepCount_of_reaches
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {M : PDA T σ γ₁}
  {c1 c2 : PDA.Config (α := T) (σ := σ) (γ := γ₁)}
-- given
  (h : M.Reaches c1 c2) :
-- imply
  ∃ n, StepCount M n c1 c2 := by
-- proof
  induction h with
  | refl => exact ⟨0, StepCount.refl _⟩
  | tail _ hs ih => obtain ⟨n, hn⟩ := ih; exact ⟨n + 1, hn.snoc hs⟩
set_option maxRecDepth 2048 in

end CFGtoPDA

namespace CFGtoPDA

/--
[step_inv_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma step_inv_aux
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {q_src : QState T g.NT}
  {w_src : List T}
  {stk_src : List (Option (Symbol T g.NT))}
  {cfg'}
-- given
  (h : (toPDA g).Step (q_src, w_src, stk_src) cfg') :
-- imply
  ∃ (q' : QState T g.NT) (a : Option T) (pop push : Option (Option (Symbol T g.NT))) (inp : List T) (stk : List (Option (Symbol T g.NT))), w_src = a.toList ++ inp ∧ stk_src = pop.toList ++ stk ∧ cfg' = (q', inp, push.toList ++ stk) ∧ (q', push) ∈ (toPDA g).step q_src a pop := by
-- proof
  generalize hc : (q_src, w_src, stk_src) = c at h
  cases h with
  | mk q q' a pop push inp stk hmem =>
    simp only [Prod.mk.injEq] at hc
    obtain ⟨hq, hinp, hstk⟩ := hc; subst hq
    exact ⟨q', a, pop, push, inp, stk, hinp, hstk, rfl, hmem⟩
set_option maxRecDepth 2048 in

end CFGtoPDA

namespace CFGtoPDA

/--
[pushing_stepCount_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma pushing_stepCount_split
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {n : ℕ}
  {L : List (Symbol T g.NT)}
  {w_arg : List T}
  {stk_arg : List (Option (Symbol T g.NT))}
  {cfg'}
-- given
  (h : StepCount (toPDA g) n (QState.pushing L, w_arg, stk_arg) cfg')
  (hn : n ≥ L.length + 1) :
-- imply
  StepCount (toPDA g) (n - (L.length + 1)) (QState.loop, w_arg, L.reverse.map some ++ stk_arg) cfg' := by
-- proof
  induction L generalizing n stk_arg with
  | nil =>
    simp only [List.length_nil, Nat.zero_add, List.reverse_nil, List.map_nil, List.nil_append]
    cases h with
    | refl => omega
    | step hs hrest =>
      simp only [Nat.add_sub_cancel]
      obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
      cases pop with
      | some _ =>
        simp [Option.toList] at hs_stk
        obtain ⟨_, _⟩ := hs_stk
        cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
      | none =>
        simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
        cases a with
        | some _ => simp [toPDA] at hmem
        | none =>
          simp [toPDA] at hmem
          obtain ⟨hq', hpush⟩ := hmem; subst hq'
          cases push with
          | none => simp [Option.toList] at hcfg; rw [hcfg] at hrest; exact hrest
          | some _ => simp at hpush
  | cons s rest ih =>
    match n, h, hn with
    | 0, .refl _, hn => omega
    | n' + 1, .step hs hrest, hn =>
      obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
      cases pop with
      | some _ =>
        simp [Option.toList] at hs_stk
        obtain ⟨_, _⟩ := hs_stk
        cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
      | none =>
        simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
        cases a with
        | some _ => simp [toPDA] at hmem
        | none =>
          simp [toPDA] at hmem
          obtain ⟨hq', hpush⟩ := hmem; subst hq'
          cases push with
          | none => simp at hpush
          | some p =>
            simp at hpush; subst hpush
            simp [Option.toList] at hcfg
            rw [hcfg] at hrest
            have hnn : n' ≥ rest.length + 1 := by simp [List.length_cons] at hn; omega
            have := ih (n := n') (stk_arg := some s :: stk_arg) hrest hnn
            simp only [List.length_cons, List.reverse_cons, List.map_append,
              List.map_cons, List.map_nil, List.append_assoc, List.singleton_append]
            convert this using 1; omega

end CFGtoPDA

namespace CFGtoPDA

/--
[pushing_needs_steps](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma pushing_needs_steps
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {k : ℕ}
  {L : List (Symbol T g.NT)}
  {w_arg : List T}
  {stk_arg : List (Option (Symbol T g.NT))}
  {cfg'}
-- given
  (h : StepCount (toPDA g) k (QState.pushing L, w_arg, stk_arg) cfg')
  (hk : k < L.length + 1) :
-- imply
  ∃ L', cfg'.1 = QState.pushing L' := by
-- proof
  induction k generalizing L w_arg stk_arg with
  | zero => cases h with | refl => exact ⟨L, rfl⟩
  | succ k' ihk =>
    cases h with
    | step hs hrest =>
      cases L with
      | nil => simp at hk
      | cons s rest_L =>
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | some _ =>
          simp [Option.toList] at hs_stk
          obtain ⟨_, _⟩ := hs_stk
          cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | none =>
          simp [Option.toList] at hs_stk hw; subst hs_stk; subst hw
          cases a with
          | some _ => simp [toPDA] at hmem
          | none =>
            simp [toPDA] at hmem
            obtain ⟨hq', hpush⟩ := hmem; subst hq'
            cases push with
            | none => simp at hpush
            | some p =>
              simp at hpush; subst hpush
              simp [Option.toList] at hcfg
              rw [hcfg] at hrest
              exact ihk (L := rest_L) hrest (by simp at hk ⊢; omega)
set_option maxRecDepth 4096 in
set_option maxHeartbeats 3200000 in

end CFGtoPDA

namespace CFGtoPDA

/--
[backward_sim_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma backward_sim_n
  {T : Type u_pda}
  {g : ContextFreeGrammar T} :
-- imply
  ∀ (n : ℕ) (γ : List (Symbol T g.NT)) (w : List T), StepCount (toPDA g) n (QState.loop, w, γ.map some ++ [none]) (QState.loop, [], [none]) → g.Derives γ (w.map Symbol.terminal) := by
-- proof
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro γ w h
    cases γ with
    | nil =>
      simp only [List.map_nil, List.nil_append] at h
      cases h with
      | refl => simp; exact Relation.ReflTransGen.refl
      | step hs hrest =>
        exfalso
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | none =>
          simp [Option.toList] at hs_stk; subst hs_stk
          cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem
        | some p =>
          simp [Option.toList] at hs_stk
          obtain ⟨hp, hstk_eq⟩ := hs_stk; subst hp; subst hstk_eq
          simp [Option.toList] at hw; subst hw
          cases a with
          | some _ => simp [toPDA] at hmem
          | none =>
            simp [toPDA] at hmem
            obtain ⟨hq', hpush⟩ := hmem; subst hq'
            cases push with
            | some _ => simp at hpush
            | none =>
              simp [Option.toList] at hcfg; rw [hcfg] at hrest
              have := hrest.to_reaches
              have := reaches_from_accept this
              simp [QState.loop, QState.accept] at this
    | cons sym γ' =>
      simp only [List.map_cons, List.cons_append] at h
      match n, h with
      | n' + 1, .step hs hrest =>
        obtain ⟨q', a, pop, push, inp, stk, hw, hs_stk, hcfg, hmem⟩ := step_inv_aux hs
        cases pop with
        | none =>
          simp [Option.toList] at hs_stk; subst hs_stk
          cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem
        | some p =>
          simp [Option.toList] at hs_stk
          obtain ⟨hp, hstk_eq⟩ := hs_stk; subst hp; subst hstk_eq
          cases sym with
          | terminal t =>
            simp [Option.toList] at hw
            cases a with
            | none => simp [toPDA] at hmem
            | some a_val =>
              simp [toPDA] at hmem
              obtain ⟨ha, hq', hpush⟩ := hmem; subst ha; subst hq'
              cases push with
              | some _ => simp at hpush
              | none =>
                simp [Option.toList] at hcfg hw
                rw [hcfg] at hrest; subst hw
                have ih_result := ih _ (by omega) γ' _ hrest
                simp only [List.map_cons]
                exact derives_cons_same (Symbol.terminal a_val) ih_result
          | nonterminal A =>
            simp [Option.toList] at hw
            cases a with
            | some _ => simp [toPDA] at hmem
            | none =>
              simp [toPDA] at hmem
              obtain ⟨r, hr_mem, hr_input, hq', hpush_eq⟩ := hmem
              subst hq'; subst hr_input
              cases push with
              | some _ => simp at hpush_eq
              | none =>
                simp [Option.toList] at hcfg hw; subst hw
                rw [hcfg] at hrest
                by_cases hn1 : n' ≥ r.output.reverse.length + 1
                · have hsplit := pushing_stepCount_split n'
                  (L := r.output.reverse) (w_arg := w)
                  (stk_arg := γ'.map some ++ [none])
                  (cfg' := (QState.loop, [], [none]))
                  hrest hn1
                  simp only [List.reverse_reverse] at hsplit
                  have hmap : r.output.map some ++ (γ'.map some ++ [none]) =
                    (r.output ++ γ').map some ++ [none] := by simp [List.map_append]
                  rw [hmap] at hsplit
                  have ih_result := ih _ (Nat.lt_of_lt_of_le (by omega) (Nat.le_refl (n' + 1))) (r.output ++ γ') w hsplit
                  have hprod : g.Produces (Symbol.nonterminal r.input :: γ') (r.output ++ γ') :=
                    ⟨r, hr_mem, ContextFreeRule.Rewrites.head γ'⟩
                  exact hprod.single.trans ih_result
                · exfalso; push_neg at hn1
                  have := pushing_needs_steps n'
                    (L := r.output.reverse) (w_arg := w)
                    (stk_arg := γ'.map some ++ [none])
                    (cfg' := (QState.loop, [], [none]))
                    hrest (by simp [List.length_reverse] at hn1 ⊢; exact hn1)
                  obtain ⟨L', hL'⟩ := this
                  simp at hL'
end CFGtoPDA
namespace CFGtoPDA
open ContextFreeGrammar ContextFreeRule
variable {T : Type u_pda}
variable {g : ContextFreeGrammar T}
set_option maxRecDepth 4096 in
set_option maxHeartbeats 1600000 in

end CFGtoPDA

namespace CFGtoPDA

/--
[stack_invariant_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma stack_invariant_step
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
  {L : List (Symbol T g.NT)}
-- given
  (hs : (toPDA g).Step c1 c2)
  (hstk : c1.2.2 = L.map some ++ [none])
  (hna1 : c1.1 ≠ QState.accept)
  (hna2 : c2.1 ≠ QState.accept)
  (hns1 : c1.1 ≠ QState.start) :
-- imply
  ∃ L' : List (Symbol T g.NT), c2.2.2 = L'.map some ++ [none] := by
-- proof
  generalize hc : c1 = cc at hs
  cases hs with
  | mk q q' a pop push inp stk hmem =>
    subst hc
    simp only [Prod.fst, Prod.snd] at hna1 hna2 hns1 hstk ⊢
    cases pop with
    | none =>
      simp [Option.toList] at hstk
      cases push with
      | none => exact ⟨L, by simp [Option.toList, hstk]⟩
      | some pv =>
        simp [Option.toList]
        cases q with
        | start => exact absurd rfl hns1
        | loop => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | pushing Lp =>
          cases Lp with
          | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | cons sp rp =>
            cases a with
            | some _ => simp [toPDA] at hmem
            | none =>
              simp [toPDA] at hmem
              obtain ⟨_, hpv⟩ := hmem; subst hpv
              exact ⟨sp :: L, by simp [hstk, List.map_cons, List.cons_append]⟩
        | accept => exact absurd rfl hna1
    | some p =>
      simp [Option.toList] at hstk
      cases L with
      | nil =>
        simp at hstk; obtain ⟨hp, hs⟩ := hstk; subst hp; subst hs
        cases q with
        | loop => cases a with
          | some _ => simp [toPDA] at hmem
          | none => simp [toPDA] at hmem; obtain ⟨hq', _⟩ := hmem; subst hq'; exact absurd rfl hna2
        | start => exact absurd rfl hns1
        | pushing Lp => cases Lp with
          | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | cons _ _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
        | accept => exact absurd rfl hna1
      | cons sL L' =>
        simp at hstk; obtain ⟨hp, hs⟩ := hstk; subst hp
        cases push with
        | none => exact ⟨L', by simp [Option.toList, hs]⟩
        | some pv =>
          simp [Option.toList]
          cases q with
          | loop =>
            cases sL with
            | terminal t => cases a with
              | none => simp [toPDA] at hmem
              | some _ => simp [toPDA] at hmem
            | nonterminal B => cases a with
              | some _ => simp [toPDA] at hmem
              | none => simp [toPDA] at hmem
          | start => exact absurd rfl hns1
          | pushing Lp => cases Lp with
            | nil => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
            | cons _ _ => cases a with | some _ => simp [toPDA] at hmem | none => simp [toPDA] at hmem
          | accept => exact absurd rfl hna1
set_option maxRecDepth 2048 in

end CFGtoPDA

namespace CFGtoPDA

/--
[no_target_start](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma no_target_start
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
-- given
  (h : (toPDA g).Step c1 c2) :
-- imply
  c2.1 ≠ QState.start := by
-- proof
  generalize hc : c1 = cc at h
  cases h with
  | mk q q' a pop push inp stk hmem =>
    subst hc; simp only [Prod.fst]
    cases q with
    | start => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
      (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.pushing])
    | accept => cases pop <;> cases a <;> simp [toPDA] at hmem
    | loop =>
      cases pop with
      | none => cases a <;> simp [toPDA] at hmem
      | some val =>
        cases val with
        | none => cases a <;> simp [toPDA] at hmem <;>
          (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.accept])
        | some sym =>
          cases sym with
          | terminal t => cases a <;> simp [toPDA] at hmem <;>
            (obtain ⟨_, hq, _⟩ := hmem; simp [hq, QState.start, QState.loop])
          | nonterminal A => cases a <;> simp [toPDA] at hmem <;>
            (obtain ⟨_, _, _, hp⟩ := hmem; simp [hp.1, QState.start, QState.pushing])
    | pushing Lp =>
      cases Lp with
      | nil => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
        (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.loop])
      | cons s rest => cases pop <;> cases a <;> simp [toPDA] at hmem <;>
        (obtain ⟨hq, _⟩ := hmem; simp [hq, QState.start, QState.pushing])

end CFGtoPDA

namespace CFGtoPDA

/--
[stack_invariant_reaches](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma stack_invariant_reaches
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {c1 c2 : PDA.Config (α := T) (σ := QState T g.NT) (γ := Option (Symbol T g.NT))}
  {L : List (Symbol T g.NT)}
-- given
  (h : (toPDA g).Reaches c1 c2)
  (hstk : c1.2.2 = L.map some ++ [none])
  (hna1 : c1.1 ≠ QState.accept)
  (hna2 : c2.1 ≠ QState.accept)
  (hns1 : c1.1 ≠ QState.start) :
-- imply
  ∃ L' : List (Symbol T g.NT), c2.2.2 = L'.map some ++ [none] := by
-- proof
  induction h with
  | refl => exact ⟨L, hstk⟩
  | @tail a_cfg b_cfg hs_prefix hs_last ih_step =>
    by_cases ha_acc : a_cfg.1 = QState.accept
    ·
      obtain ⟨q_a, w_a, stk_a⟩ := a_cfg; simp at ha_acc; subst ha_acc
      exact absurd hs_last no_step_from_accept
    · obtain ⟨L', hL'⟩ := ih_step ha_acc
      have hns_a : a_cfg.1 ≠ QState.start := by
        intro heq
        cases Relation.ReflTransGen.cases_tail hs_prefix with
        | inl h_eq => rw [h_eq] at heq; exact hns1 heq
        | inr h_ex =>
          obtain ⟨mid, _, hmid_step⟩ := h_ex
          exact no_target_start hmid_step heq
      exact stack_invariant_step hs_last hL' ha_acc hna2 hns_a
set_option maxRecDepth 4096 in
set_option maxHeartbeats 6400000 in

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_language_backward_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_language_backward_aux
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {w : List T}
  {stk : List (Option (Symbol T g.NT))} :
-- imply
  (CFGtoPDA.toPDA g).Reaches (CFGtoPDA.QState.start, w, []) (CFGtoPDA.QState.accept, [], stk) → g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
-- proof
  intro hreach
  cases Relation.ReflTransGen.cases_head hreach with
  | inl heq => simp [QState.start, QState.accept] at heq
  | inr hex =>
    obtain ⟨mid1, hstep1, hrest1⟩ := hex
    obtain ⟨q1', a1, pop1, push1, inp1, stk1, hw1, hs1, hcfg1, hmem1⟩ := step_inv_aux hstep1
    cases pop1 with
    | some _ => simp [Option.toList] at hs1
    | none =>
      simp [Option.toList] at hs1 hw1; subst hs1; subst hw1
      cases a1 with
      | some _ => simp [toPDA] at hmem1
      | none =>
        simp [toPDA] at hmem1
        obtain ⟨hq1', hpush1⟩ := hmem1; subst hq1'
        cases push1 with
        | none => simp at hpush1
        | some p1 =>
          simp at hpush1; subst hpush1
          simp [Option.toList] at hcfg1
          rw [hcfg1] at hrest1
          cases Relation.ReflTransGen.cases_tail hrest1 with
          | inl heq => simp [QState.pushing, QState.accept] at heq
          | inr hex2 =>
            obtain ⟨mid2, hrest2, hstep2⟩ := hex2
            generalize hc_acc : (QState.accept, ([] : List T), stk) = cfg_acc at hstep2
            cases hstep2 with
            | mk q2 q2' a2 pop2 push2 inp2 stk2 hmem2 =>
              simp only [Prod.mk.injEq] at hc_acc
              obtain ⟨hq2_acc, hinp2, hstk2_eq⟩ := hc_acc; subst hq2_acc
              cases pop2 with
              | none =>
                simp [Option.toList] at *
                cases q2 with
                | start => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.pushing] at h1)
                | accept => cases a2 <;> simp [toPDA] at hmem2
                | loop => cases a2 <;> simp [toPDA] at hmem2
                | pushing Lp =>
                  cases Lp with
                  | nil => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop] at h1)
                  | cons _ _ => cases a2 <;> simp [toPDA] at hmem2 <;> (obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.pushing] at h1)
              | some p2 =>
                simp [Option.toList] at *
                cases q2 with
                | start => cases a2 <;> simp [toPDA] at hmem2
                | accept => cases a2 <;> simp [toPDA] at hmem2
                | pushing Lp2 =>
                  cases Lp2 with
                  | nil => cases a2 <;> simp [toPDA] at hmem2 <;>
                    (try obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop, QState.pushing] at h1)
                  | cons _ _ => cases a2 <;> simp [toPDA] at hmem2 <;>
                    (try obtain ⟨h1, _⟩ := hmem2; simp [QState.accept, QState.loop, QState.pushing] at h1)
                | loop =>
                  cases p2 with
                  | some ss2 =>
                    cases ss2 with
                    | terminal t2 => cases a2 with
                      | none => simp [toPDA] at hmem2
                      | some _ => simp [toPDA] at hmem2
                    | nonterminal B2 => cases a2 with
                      | some _ => simp [toPDA] at hmem2
                      | none => simp [toPDA] at hmem2
                  | none =>
                    cases a2 with
                    | some _ => simp [toPDA] at hmem2
                    | none =>
                      simp [toPDA] at hmem2
                      subst hmem2
                      simp [Option.toList] at hinp2 hstk2_eq hrest2
                      subst hinp2; subst hstk2_eq
                      have hgood := stack_invariant_reaches hrest2
                        (L := []) (by simp)
                        (by simp [QState.pushing, QState.accept])
                        (by simp [QState.loop, QState.accept])
                        (by simp [QState.pushing, QState.start])
                      obtain ⟨L', hL'⟩ := hgood
                      simp at hL'
                      cases L' with
                      | nil =>
                        simp at hL'; subst hL'
                        obtain ⟨m, hm⟩ := stepCount_of_reaches hrest2
                        have hm_ge : m ≥ 2 := by
                          by_contra hlt; push_neg at hlt
                          have := pushing_needs_steps m (L := [Symbol.nonterminal g.initial])
                            (w_arg := inp1) (stk_arg := [none]) (cfg' := (QState.loop, [], [none]))
                            hm (by simpa using hlt)
                          obtain ⟨L', hL''⟩ := this
                          simp at hL''
                        have hsplit := pushing_stepCount_split m
                          (L := [Symbol.nonterminal g.initial]) (w_arg := inp1)
                          (stk_arg := [none])
                          (cfg' := (QState.loop, [], [none]))
                          hm hm_ge
                        simp only [List.length_cons, List.length_nil, List.reverse_cons,
                          List.reverse_nil, List.nil_append, List.map_cons, List.map_nil,
                          List.singleton_append] at hsplit
                        exact backward_sim_n (m - 2) [Symbol.nonterminal g.initial] inp1 hsplit
                      | cons _ _ => simp at hL'

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_language_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_language_backward
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {w : List T} :
-- imply
  (toPDA g).Accepts w → g.Derives [Symbol.nonterminal g.initial] (w.map Symbol.terminal) := by
-- proof
  intro ⟨q, hq, stk, hreach⟩
  simp [toPDA] at hq; subst hq
  exact toPDA_language_backward_aux g w stk hreach
set_option maxRecDepth 2048 in

end CFGtoPDA

namespace CFGtoPDA

/--
[toPDA_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma toPDA_language
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T} :
-- imply
  (CFGtoPDA.toPDA g).language = g.language := by
-- proof
  ext w
  simp only [PDA.language, PDA.Accepts, ContextFreeGrammar.mem_language_iff]
  constructor
  · exact toPDA_language_backward g w
  · intro hderiv
    obtain ⟨n, hn⟩ := derives_to_derivesIn' hderiv
    refine ⟨QState.accept, Set.mem_singleton _, [], ?_⟩
    apply Relation.ReflTransGen.head
    · have h := PDA.Step.mk (M := toPDA g) QState.start
      (QState.pushing [Symbol.nonterminal g.initial])
      (none : Option T) (none : Option (Option (Symbol T g.NT)))
      (some none) w [] (by simp [toPDA])
      simpa [Option.toList] using h
    apply Relation.ReflTransGen.trans
    · exact toPDA_push_list [Symbol.nonterminal g.initial] w [none]
    simp only [List.reverse_cons, List.reverse_nil, List.nil_append, List.map_cons,
      List.map_nil, List.singleton_append]
    apply Relation.ReflTransGen.trans
    · have := @toPDA_simulates T g n [Symbol.nonterminal g.initial] w [none] hn
      simpa [List.map] using this
    apply Relation.ReflTransGen.single
    · have h := PDA.Step.mk (M := toPDA g) QState.loop QState.accept
      (none : Option T) (some (none : Option (Symbol T g.NT))) none [] []
      (by simp [toPDA])
      simpa [Option.toList] using h

end CFGtoPDA

namespace CFGtoPDA

/--
[cfg_to_pda](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/CFGtoPDA.lean)
-/
@[path]
lemma cfg_to_pda
  {T : Type u_pda}
  {g : ContextFreeGrammar T}
  {A : Language T}
-- given
  (h : ContextFree.IsContextFree A) :
-- imply
  IsPDARecognizable A := by
-- proof
  obtain ⟨g, rfl⟩ := h
  exact ⟨_, _, toPDA g, toPDA_language g⟩

end CFGtoPDA


-- created on 2026-10-23
