import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TheoryOfComputation.code.ContextFree.Part4
open ChomskyNormalForm CFLPumping CFLPumping.CNFParseTree


namespace ChomskyNormalForm

/--
[ntCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma ntCount_append
  {l₁ l₂ : List (Symbol T N)} :
-- imply
  ntCount (l₁ ++ l₂) = ntCount l₁ + ntCount l₂ := by
-- proof
  induction l₁ with
  | nil => simp [ntCount]
  | cons s rest ih =>
    cases s with
    | terminal a => simp [ntCount, ih]
    | nonterminal A => simp [ntCount, ih]; omega

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[tCount_append](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma tCount_append
  {l₁ l₂ : List (Symbol T N)} :
-- imply
  tCount (l₁ ++ l₂) = tCount l₁ + tCount l₂ := by
-- proof
  induction l₁ with
  | nil => simp [tCount]
  | cons s rest ih =>
    cases s with
    | terminal a => simp [tCount, ih]; omega
    | nonterminal A => simp [tCount, ih]

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[ntCount_map_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma ntCount_map_terminal
  {w : List T} :
-- imply
  ntCount (N := N) (w.map Symbol.terminal) = 0 := by
-- proof
  induction w with
  | nil => simp [ntCount]
  | cons a rest ih => simp [ntCount, ih]

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[tCount_map_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma tCount_map_terminal
  {w : List T} :
-- imply
  tCount (N := N) (w.map Symbol.terminal) = w.length := by
-- proof
  induction w with
  | nil => simp [tCount]
  | cons a rest ih => simp [tCount, ih]; omega

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[cnf_start_not_in_output](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_start_not_in_output
  {g : ContextFreeGrammar T}
  {r : ContextFreeRule T g.NT}
-- given
  (hcnf : IsCNF g)
  (hr : r ∈ g.rules) :
-- imply
  Symbol.nonterminal g.initial ∉ r.output := by
-- proof
  have hcnf_r := hcnf r hr
  obtain ⟨B, C, hB, hC, hout⟩ | ⟨a, hout⟩ | ⟨_, hout⟩ := hcnf_r
  · rw [hout]
    intro hmem
    simp only [List.mem_cons, List.mem_nil_iff, or_false, Symbol.nonterminal.injEq] at hmem
    obtain h | h := hmem
    · exact hB (Eq.symm h)
    · exact hC (Eq.symm h)
  · rw [hout]; simp
  · rw [hout]; simp

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[cnf_start_not_in_produces](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_start_not_in_produces
  {g : ContextFreeGrammar T}
  {sf v : List (Symbol T g.NT)}
-- given
  (hcnf : IsCNF g)
  (hp : g.Produces sf v)
  (hsf : Symbol.nonterminal g.initial ∉ sf) :
-- imply
  Symbol.nonterminal g.initial ∉ v := by
-- proof
  obtain ⟨r, hr_mem, hrw⟩ := hp
  rw [ContextFreeRule.rewrites_iff] at hrw
  obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw
  rw [hpq_out]
  intro hmem
  simp only [List.mem_append] at hmem
  obtain (h | h) | h := hmem
  · exact hsf (by rw [hpq_in]; simp [List.mem_append]; left; exact h)
  · exact cnf_start_not_in_output g hcnf r hr_mem h
  · exact hsf (by rw [hpq_in]; simp [List.mem_append]; right; right; exact h)

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[cnf_produces_cost_step](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_produces_cost_step
  {g : ContextFreeGrammar T}
  {sf v : List (Symbol T g.NT)}
-- given
  (hcnf : IsCNF g)
  (hp : g.Produces sf v)
  (hsf : Symbol.nonterminal g.initial ∉ sf) :
-- imply
  2 * tCount v + ntCount v = 2 * tCount sf + ntCount sf + 1 := by
-- proof
  obtain ⟨r, hr_mem, hrw⟩ := hp
  rw [ContextFreeRule.rewrites_iff] at hrw
  obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw
  have hcnf_r := hcnf r hr_mem
  rw [hpq_in, hpq_out]
  simp only [ntCount_append, tCount_append]
  obtain ⟨B, C, _, _, hout⟩ | ⟨a, hout⟩ | ⟨hinp, hout⟩ := hcnf_r
  ·
    rw [hout]; simp [ntCount, tCount]; omega
  ·
    rw [hout]; simp [ntCount, tCount]; omega
  ·
    exfalso
    have : Symbol.nonterminal r.input ∈ sf := by
      rw [hpq_in]; simp [List.mem_append]
    rw [hinp] at this
    exact hsf this

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[cnf_derivesIn_cost](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_derivesIn_cost
  {g : ContextFreeGrammar T}
  {sf w : List (Symbol T g.NT)}
  {n : ℕ}
-- given
  (hcnf : IsCNF g)
  (hd : DerivesIn g sf w n)
  (hsf : Symbol.nonterminal g.initial ∉ sf) :
-- imply
  2 * tCount w + ntCount w = 2 * tCount sf + ntCount sf + n := by
-- proof
  induction hd with
  | refl _ => omega
  | step hp hd' ih =>
    have hsf' := cnf_start_not_in_produces g hcnf hp hsf
    have hih := ih hsf'
    have hcost := cnf_produces_cost_step g hcnf hp hsf
    omega

end ChomskyNormalForm

namespace ChomskyNormalForm

/--
[cnf_derivation_length](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_derivation_length
  {g : ContextFreeGrammar T}
  {w : List T}
  {n : ℕ}
-- given
  (hcnf : IsCNF g)
  (hw : w ≠ [])
  (hw_mem : w ∈ g.language)
  (hderiv : DerivesIn g [Symbol.nonterminal g.initial] (w.map Symbol.terminal) n) :
-- imply
  n = 2 * w.length - 1 := by
-- proof
  have hne_sf : [Symbol.nonterminal g.initial] ≠ w.map Symbol.terminal := by
    intro heq
    have : Symbol.nonterminal g.initial ∈ w.map Symbol.terminal := by
      rw [← heq]; simp
    simp only [List.mem_map] at this
    obtain ⟨_, _, habs⟩ := this
    cases habs
  obtain ⟨v, n', hp, hd, rfl⟩ : ∃ v n', g.Produces [Symbol.nonterminal g.initial] v ∧
    DerivesIn g v (w.map Symbol.terminal) n' ∧ n = n' + 1 := by
    generalize hs : [Symbol.nonterminal g.initial] = s at hderiv
    cases hderiv with
    | refl => exact absurd (Eq.symm hs) (Ne.symm hne_sf)
    | step hp hd => exact ⟨_, _, hs ▸ hp, hd, rfl⟩
  obtain ⟨r, hr_mem, hrw⟩ := hp
  rw [ContextFreeRule.rewrites_iff] at hrw
  obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw
  have hp_nil : p = [] := by
    by_contra h
    have hlen := congr_arg List.length hpq_in
    simp [List.length_append] at hlen
    cases p with
    | nil => exact h rfl
    | cons _ _ => simp [List.length_append] at hlen; omega
  have hq_nil : q = [] := by
    rw [hp_nil] at hpq_in; simp at hpq_in; exact hpq_in.2
  have hv_eq : v = r.output := by
    rw [hp_nil, hq_nil] at hpq_out; simpa using hpq_out
  have hsv : Symbol.nonterminal g.initial ∉ v := by
    rw [hv_eq]; exact cnf_start_not_in_output g hcnf r hr_mem
  have hcost := cnf_derivesIn_cost g hcnf hd hsv
  have hcnf_r := hcnf r hr_mem
  obtain ⟨B, C, _, _, hout⟩ | ⟨a, hout⟩ | ⟨_, hout⟩ := hcnf_r
  ·
    rw [hv_eq, hout] at hcost
    simp [ntCount, tCount, ntCount_map_terminal, tCount_map_terminal] at hcost
    omega
  ·
    rw [hv_eq, hout] at hcost
    simp [ntCount, tCount, ntCount_map_terminal, tCount_map_terminal] at hcost
    omega
  ·
    exfalso
    rw [hv_eq, hout] at hd
    suffices h : (w.map (Symbol.terminal (N := g.NT))) = ([] : List (Symbol T g.NT)) by
      simp at h; exact hw h
    generalize ht : (w.map (Symbol.terminal (N := g.NT))) = t at hd
    generalize hw' : ([] : List (Symbol T g.NT)) = s' at hd
    induction hd with
    | refl => rfl
    | step hp' _ _ =>
      obtain ⟨r', _, hrw'⟩ := hp'
      rw [ContextFreeRule.rewrites_iff] at hrw'
      obtain ⟨p', _, hpq', _⟩ := hrw'
      rw [← hw'] at hpq'; simp [List.append_assoc] at hpq'
end ChomskyNormalForm
universe u v w


/--
[listPow_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma listPow_succ
  {l : List α}
  {n : Nat} :
-- imply
  listPow l (n + 1) = l ++ listPow l n :=
-- proof
  rfl

/--
[listPow_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma listPow_comm
  {l : List α} :
-- imply
  ∀ n, l ++ listPow l n = listPow l n ++ l := by
-- proof
  intro n
  induction n with
  | zero => simp [listPow]
  | succ n ih =>
    show l ++ (l ++ listPow l n) = (l ++ listPow l n) ++ l
    rw [List.append_assoc, ih]

/--
[listPow_succ_right](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma listPow_succ_right
  {l : List α}
  {n : Nat} :
-- imply
  listPow l (n + 1) = listPow l n ++ l :=
-- proof
  listPow_comm l n
namespace CFLPumping
variable {T : Type*}
section PumpIteration
variable {g : ContextFreeGrammar T}

namespace CFLPumping

/--
[derives_pump_once](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma derives_pump_once
  {g : ContextFreeGrammar T}
  {A : g.NT}
  {u v target : List (Symbol T g.NT)}
-- given
  (hloop : g.Derives [Symbol.nonterminal A] (u ++ [Symbol.nonterminal A] ++ v))
  (htarget : g.Derives [Symbol.nonterminal A] target) :
-- imply
  g.Derives [Symbol.nonterminal A] (u ++ target ++ v) :=
-- proof
  hloop.trans ((htarget.append_left u).append_right v)

end CFLPumping

namespace CFLPumping

/--
[derives_pump_iter](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma derives_pump_iter
  {g : ContextFreeGrammar T}
  {A : g.NT}
  {u v target : List (Symbol T g.NT)}
  {i : ℕ}
-- given
  (hloop : g.Derives [Symbol.nonterminal A] (u ++ [Symbol.nonterminal A] ++ v))
  (htarget : g.Derives [Symbol.nonterminal A] target) :
-- imply
  g.Derives [Symbol.nonterminal A] (listPow u i ++ target ++ listPow v i) := by
-- proof
  induction i with
  | zero => simpa [listPow] using htarget
  | succ n ih =>
    have h := derives_pump_once hloop ih
    rw [listPow_succ, listPow_succ_right v n]
    simp only [List.append_assoc] at h ⊢
    exact h
end PumpIteration
section DecompositionHelpers

end CFLPumping

namespace CFLPumping

/--
[produces_append_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma produces_append_split
  {g : ContextFreeGrammar T}
  {u v w : List (Symbol T g.NT)}
-- given
  (h : g.Produces (u ++ v) w) :
-- imply
  (∃ u', w = u' ++ v ∧ g.Produces u u') ∨ (∃ v', w = u ++ v' ∧ g.Produces v v') := by
-- proof
  obtain ⟨r, hr_mem, hrw⟩ := h
  rw [ContextFreeRule.rewrites_iff] at hrw
  obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw
  have hpq_in' : u ++ v = p ++ ([Symbol.nonterminal r.input] ++ q) := by
    simp only [List.append_assoc] at hpq_in ⊢; exact hpq_in
  rw [List.append_eq_append_iff] at hpq_in'
  cases hpq_in' with
  | inl h =>
    obtain ⟨as, hp, hv⟩ := h
    right
    refine ⟨as ++ r.output ++ q, ?_, ?_⟩
    · rw [hpq_out, hp]; simp [List.append_assoc]
    · refine ⟨r, hr_mem, ?_⟩
      rw [ContextFreeRule.rewrites_iff]
      exact ⟨as, q, by rwa [List.append_assoc], rfl⟩
  | inr h =>
    obtain ⟨bs, hu, hbsv⟩ := h
    cases bs with
    | nil =>
      simp at hbsv
      right
      refine ⟨r.output ++ q, ?_, ?_⟩
      · rw [hpq_out, hu]; simp [List.append_assoc]
      · refine ⟨r, hr_mem, ?_⟩
        rw [ContextFreeRule.rewrites_iff]
        refine ⟨[], q, ?_, rfl⟩
        simp; exact hbsv.symm
    | cons b bs' =>
      simp at hbsv
      obtain ⟨hb, hbs'v⟩ := hbsv
      left
      refine ⟨p ++ r.output ++ bs', ?_, ?_⟩
      · rw [hpq_out, hbs'v]; simp [List.append_assoc]
      · refine ⟨r, hr_mem, ?_⟩
        rw [ContextFreeRule.rewrites_iff]
        refine ⟨p, bs', ?_, rfl⟩
        rw [hu, ← hb]; simp [List.append_assoc]

end CFLPumping

namespace CFLPumping

/--
[derives_append_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma derives_append_split
  {g : ContextFreeGrammar T}
  {u v w : List (Symbol T g.NT)}
-- given
  (h : g.Derives (u ++ v) w) :
-- imply
  ∃ w1 w2, w = w1 ++ w2 ∧ g.Derives u w1 ∧ g.Derives v w2 := by
-- proof
  induction h with
  | refl => exact ⟨u, v, rfl, .refl u, .refl v⟩
  | tail _ hlast ih =>
    obtain ⟨w1, w2, heq, hd1, hd2⟩ := ih
    subst heq
    cases produces_append_split hlast with
    | inl h =>
      obtain ⟨w1', hw, hp⟩ := h
      exact ⟨w1', w2, hw, hd1.trans_produces hp, hd2⟩
    | inr h =>
      obtain ⟨w2', hw, hp⟩ := h
      exact ⟨w1, w2', hw, hd1, hd2.trans_produces hp⟩

end CFLPumping

namespace CFLPumping

/--
[all_terminals_not_produces](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma all_terminals_not_produces
  {g : ContextFreeGrammar T}
  {w : List T}
  {v : List (Symbol T g.NT)}
-- given
  (h : g.Produces (w.map Symbol.terminal) v) :
-- imply
  False := by
-- proof
  obtain ⟨r, _, hrw⟩ := h
  exact absurd hrw.nonterminal_input_mem (by simp [List.mem_map])

end CFLPumping

namespace CFLPumping

/--
[map_terminal_split](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma map_terminal_split
  {g : ContextFreeGrammar T}
  {w : List T}
  {w1 w2 : List (Symbol T N)}
-- given
  (h : w.map Symbol.terminal = w1 ++ w2) :
-- imply
  ∃ a b : List T, w1 = a.map Symbol.terminal ∧ w2 = b.map Symbol.terminal ∧ w = a ++ b := by
-- proof
  induction w generalizing w1 w2 with
  | nil =>
    simp at h
    obtain ⟨h1, h2⟩ := h; subst h1; subst h2
    exact ⟨[], [], rfl, rfl, rfl⟩
  | cons t w ih =>
    cases w1 with
    | nil => simp at h; exact ⟨[], t :: w, rfl, by simp [h], rfl⟩
    | cons s w1' =>
      simp at h
      obtain ⟨hs, hrest⟩ := h
      obtain ⟨a', b', ha', hb', hw'⟩ := ih w1' w2 hrest
      exact ⟨t :: a', b', by simp [← hs, ha'], hb', by simp [hw']⟩

end CFLPumping

namespace CFLPumping.CNFParseTree

/--
[yield_length_le_pow_height](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma yield_length_le_pow_height
  {g : ContextFreeGrammar T}
  {t : CNFParseTree g A} :
-- imply
  t.yield.length ≤ 2 ^ t.height := by
-- proof
  induction t with
  | leaf _ a _ => simp [yield, height]
  | node _ _ _ _ l r ihl ihr =>
    simp only [yield, height, List.length_append]
    have hle1 : l.yield.length + r.yield.length
      ≤ 2 ^ (max l.height r.height) + 2 ^ (max l.height r.height) := by
      calc l.yield.length + r.yield.length
        ≤ 2 ^ l.height + 2 ^ r.height := Nat.add_le_add ihl ihr
        _ ≤ 2 ^ (max l.height r.height) + 2 ^ (max l.height r.height) := by
          apply Nat.add_le_add
          · apply Nat.pow_le_pow_right (by omega : 1 ≤ 2) (le_max_left _ _)
          · apply Nat.pow_le_pow_right (by omega : 1 ≤ 2) (le_max_right _ _)
    calc l.yield.length + r.yield.length
      ≤ 2 ^ (max l.height r.height) + 2 ^ (max l.height r.height) := hle1
      _ = 2 * 2 ^ (max l.height r.height) := by omega
      _ = 2 ^ (max l.height r.height + 1) := by rw [Nat.pow_succ, Nat.mul_comm]

end CFLPumping.CNFParseTree

namespace CFLPumping.CNFParseTree

/--
[tree_derives](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma tree_derives
  {g : ContextFreeGrammar T}
  {t : CNFParseTree g A} :
-- imply
  g.Derives [Symbol.nonterminal A] (t.yield.map Symbol.terminal) := by
-- proof
  induction t with
  | leaf A a hr =>
    apply Relation.ReflTransGen.single
    exact ⟨⟨A, [Symbol.terminal a]⟩, hr, ContextFreeRule.Rewrites.input_output⟩
  | node A B C hr l r ihl ihr =>
    simp only [yield, List.map_append]
    exact (Relation.ReflTransGen.single
      ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans
      ((ihl.append_right _).trans (ihr.append_left _))

end CFLPumping.CNFParseTree

namespace CFLPumping.CNFParseTree

/--
[yield_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma yield_nonempty
  {g : ContextFreeGrammar T}
  {t : CNFParseTree g A} :
-- imply
  t.yield ≠ [] := by
-- proof
  cases t with
  | leaf => simp [yield]
  | node _ _ _ _ l _ =>
    simp only [yield]
    exact List.append_ne_nil_of_left_ne_nil l.yield_nonempty _

end CFLPumping.CNFParseTree

namespace CFLPumping.CNFParseTree

/--
[exists_decomp_nonempty_ctx](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma exists_decomp_nonempty_ctx
  {g : ContextFreeGrammar T}
  {t : CNFParseTree g A}
  {d : ℕ}
-- given
  (hd : d ≤ t.height)
  (hd_pos : 0 < d) :
-- imply
  ∃ (R : g.NT) (sub : CNFParseTree g R) (lc rc : List T), R = t.ntAtDepth d hd ∧ sub.height = t.height - d ∧ t.yield = lc ++ sub.yield ++ rc ∧ g.Derives [Symbol.nonterminal A] (lc.map Symbol.terminal ++ [Symbol.nonterminal R] ++ rc.map Symbol.terminal) ∧ (lc ++ rc).length > 0 := by
-- proof
  induction d generalizing A with
  | zero => omega
  | succ d ih =>
    cases t with
    | leaf _ _ hr => simp [height] at hd
    | node A B C hr l r =>
      simp only [height] at hd
      by_cases h : l.height ≥ r.height
      · have hd' : d ≤ l.height := by omega
        obtain rfl | hd_pos' := Nat.eq_zero_or_pos d
        · exact ⟨B, l, [], r.yield,
          by simp only [ntAtDepth, h, ↓reduceDIte],
          by simp [height]; omega,
          by simp [yield],
          by simp only [List.map_nil, List.nil_append]
            exact (Relation.ReflTransGen.single
              ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans
              (r.tree_derives.append_left [Symbol.nonterminal B]),
          List.length_pos_of_ne_nil r.yield_nonempty⟩
        · obtain ⟨R, sub, lc', rc', hR, hsub, hyield, hderives, hctx⟩ := ih l hd' hd_pos'
          exact ⟨R, sub, lc', rc' ++ r.yield,
            by simp only [ntAtDepth, h, ↓reduceDIte, hR],
            by simp only [height]; omega,
            by simp only [yield, hyield, List.append_assoc],
            by have step2 := hderives.append_right [Symbol.nonterminal C]
              have step3 := r.tree_derives.append_left
                (lc'.map Symbol.terminal ++ [Symbol.nonterminal R] ++ rc'.map Symbol.terminal)
              simp only [List.map_append, List.append_assoc] at step2 step3 ⊢
              exact (Relation.ReflTransGen.single
                ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans (step2.trans step3),
            by simp only [List.length_append] at hctx ⊢; omega⟩
      · simp only [not_le] at h
        have hd' : d ≤ r.height := by omega
        obtain rfl | hd_pos' := Nat.eq_zero_or_pos d
        · exact ⟨C, r, l.yield, [],
          by simp only [ntAtDepth, not_le.mpr h, ↓reduceDIte],
          by simp [height]; omega,
          by simp [yield],
          by simp only [List.map_nil, List.append_nil]
            exact (Relation.ReflTransGen.single
              ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans
              (l.tree_derives.append_right [Symbol.nonterminal C]),
          by simp only [List.length_append, List.length_nil, Nat.add_zero]
            exact List.length_pos_of_ne_nil l.yield_nonempty⟩
        · obtain ⟨R, sub, lc', rc', hR, hsub, hyield, hderives, hctx⟩ := ih r hd' hd_pos'
          exact ⟨R, sub, l.yield ++ lc', rc',
            by simp only [ntAtDepth, not_le.mpr h, ↓reduceDIte, hR],
            by simp only [height]; omega,
            by simp only [yield, hyield, List.append_assoc],
            by have step2 := l.tree_derives.append_right [Symbol.nonterminal C]
              have step3 := hderives.append_left (l.yield.map Symbol.terminal)
              simp only [List.map_append, List.append_assoc] at step2 step3 ⊢
              exact (Relation.ReflTransGen.single
                ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans (step2.trans step3),
            by simp only [List.length_append] at hctx ⊢; omega⟩

end CFLPumping.CNFParseTree

namespace CFLPumping.CNFParseTree

/--
[ntAtDepth_node_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma ntAtDepth_node_eq
  {g : ContextFreeGrammar T}
  {A B C : g.NT}
  {l : CNFParseTree g B}
  {r : CNFParseTree g C}
  {n : ℕ}
-- given
  (hr : ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ ∈ g.rules)
  (hn : 0 < n)
  (hd : n ≤ (node A B C hr l r).height) :
-- imply
  (node A B C hr l r).ntAtDepth n hd = if h : l.height ≥ r.height then l.ntAtDepth (n - 1) (by simp [height] at hd; omega) else r.ntAtDepth (n - 1) (by simp [height] at hd; omega) := by
-- proof
  cases n with
  | zero => omega
  | succ n => simp only [ntAtDepth, Nat.succ_sub_one]

end CFLPumping.CNFParseTree

namespace CFLPumping.CNFParseTree

/--
[exists_decomp_with_coherence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma exists_decomp_with_coherence
  {g : ContextFreeGrammar T}
  {t : CNFParseTree g A}
  {d1 d2 : ℕ}
-- given
  (hd1 : d1 ≤ t.height)
  (hd12 : d1 + d2 ≤ t.height) :
-- imply
  ∃ (R : g.NT) (sub : CNFParseTree g R) (lc rc : List T), R = t.ntAtDepth d1 hd1 ∧ sub.height = t.height - d1 ∧ t.yield = lc ++ sub.yield ++ rc ∧ g.Derives [Symbol.nonterminal A] (lc.map Symbol.terminal ++ [Symbol.nonterminal R] ++ rc.map Symbol.terminal) ∧ (∀ hd2 : d2 ≤ sub.height, sub.ntAtDepth d2 hd2 = t.ntAtDepth (d1 + d2) hd12) := by
-- proof
  induction d1 generalizing A with
  | zero =>
    cases t with
    | leaf A a hr =>
      exact ⟨A, .leaf A a hr, [], [], rfl, rfl, by simp [yield], .refl _,
        fun _ => by congr 1; omega⟩
    | node A B C hr l r =>
      exact ⟨A, .node A B C hr l r, [], [], rfl, rfl, by simp [yield], .refl _,
        fun _ => by congr 1; omega⟩
  | succ d1 ih =>
    cases t with
    | leaf _ _ _ => simp [height] at hd1
    | node A B C hr l r =>
      simp only [height] at hd1 hd12
      by_cases h : l.height ≥ r.height
      · have hd1' : d1 ≤ l.height := by omega
        have hd12' : d1 + d2 ≤ l.height := by omega
        obtain ⟨R, sub, lc', rc', hR, hsub, hyield, hderives, hcoh⟩ := ih l hd1' hd12'
        refine ⟨R, sub, lc', rc' ++ r.yield, ?_, ?_, ?_, ?_, ?_⟩
        · rw [hR]; simp only [ntAtDepth, h, ↓reduceDIte]
        · rw [hsub]; simp [height]; omega
        · simp only [yield, hyield, List.append_assoc]
        · have step2 := hderives.append_right [Symbol.nonterminal C]
          have step3 := r.tree_derives.append_left
            (lc'.map Symbol.terminal ++ [Symbol.nonterminal R] ++ rc'.map Symbol.terminal)
          simp only [List.map_append, List.append_assoc] at step2 step3 ⊢
          exact (Relation.ReflTransGen.single
            ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans (step2.trans step3)
        · intro hd2
          rw [hcoh (by rw [hsub]; omega)]
          rw [ntAtDepth_node_eq hr l r _ (by omega) hd12, dif_pos h]
          congr 1; omega
      · have hnotge : ¬(l.height ≥ r.height) := h
        have hd1' : d1 ≤ r.height := by simp only [not_le] at h; omega
        have hd12' : d1 + d2 ≤ r.height := by simp only [not_le] at h; omega
        obtain ⟨R, sub, lc', rc', hR, hsub, hyield, hderives, hcoh⟩ := ih r hd1' hd12'
        refine ⟨R, sub, l.yield ++ lc', rc', ?_, ?_, ?_, ?_, ?_⟩
        · rw [hR]; simp only [ntAtDepth, hnotge, ↓reduceDIte]
        · rw [hsub]; simp [height]; simp only [not_le] at h; omega
        · simp only [yield, hyield, List.append_assoc]
        · have step2 := l.tree_derives.append_right [Symbol.nonterminal C]
          have step3 := hderives.append_left (l.yield.map Symbol.terminal)
          simp only [List.map_append, List.append_assoc] at step2 step3 ⊢
          exact (Relation.ReflTransGen.single
            ⟨⟨A, _⟩, hr, ContextFreeRule.Rewrites.input_output⟩).trans (step2.trans step3)
        · intro hd2
          rw [hcoh (by rw [hsub]; omega)]
          rw [ntAtDepth_node_eq hr l r _ (by omega) hd12, dif_neg hnotge]
          congr 1; omega

end CFLPumping.CNFParseTree

namespace CFLPumping

/--
[produces_from_singleton_nonterminal'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma produces_from_singleton_nonterminal'
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {A : g.NT}
  {v : List (Symbol T g.NT)}
-- given
  (h : g.Produces [Symbol.nonterminal A] v) :
-- imply
  ∃ r ∈ g.rules, r.input = A ∧ v = r.output := by
-- proof
  obtain ⟨r, hr_mem, hrw⟩ := h
  obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw.exists_parts
  have hlen : p.length + 1 + q.length = 1 := by
    have := congr_arg List.length hpq_in
    simp [List.length_append] at this; omega
  have hp : p = [] := by
    obtain _ | ⟨_, _⟩ <;> simp_all <;> omega := p
  have hq : q = [] := by
    subst hp; simp at hlen
    obtain _ | ⟨_, _⟩ <;> simp_all <;> omega := q
  subst hp; subst hq
  simp at hpq_in hpq_out
  exact ⟨r, hr_mem, hpq_in.symm, hpq_out⟩

end CFLPumping

namespace CFLPumping

/--
[derives_from_nt_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma derives_from_nt_nontrivial
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {A : g.NT}
  {w : List T}
-- given
  (hne : w ≠ [])
  (hd : g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal)) :
-- imply
  ∃ v, g.Produces [Symbol.nonterminal A] v ∧ g.Derives v (w.map Symbol.terminal) := by
-- proof
  obtain h | ⟨v, hprod, hrest⟩ := hd.eq_or_head
  · exfalso
    cases w with
    | nil => exact hne rfl
    | cons t ts => simp at h
  · exact ⟨v, hprod, hrest⟩

end CFLPumping

namespace CFLPumping

/--
[derives_nil_of_nil](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma derives_nil_of_nil
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {w : List (Symbol T g.NT)}
-- given
  (hd : g.Derives [] w) :
-- imply
  w = [] := by
-- proof
  obtain h | ⟨v, hprod, _⟩ := hd.eq_or_head
  · exact h.symm
  · exfalso
    obtain ⟨r, _, hrw⟩ := hprod
    have := hrw.nonterminal_input_mem
    simp at this

end CFLPumping

namespace CFLPumping

/--
[cnf_nonempty_of_derives_ne_initial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_nonempty_of_derives_ne_initial
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {B : g.NT}
  {w : List (Symbol T g.NT)}
-- given
  (hcnf : ChomskyNormalForm.IsCNF g)
  (hB : B ≠ g.initial)
  (hd : g.Derives [Symbol.nonterminal B] w) :
-- imply
  w ≠ [] := by
-- proof
  intro hw
  subst hw
  obtain h | ⟨u, hderiv_u, hprod_u⟩ := hd.eq_or_tail
  · simp at h
  · obtain ⟨r, hr_mem, hrw⟩ := hprod_u
    obtain ⟨p, q, hpq_in, hpq_out⟩ := hrw.exists_parts
    have hp : p = [] := by
      cases p with
      | nil => rfl
      | cons _ _ => simp [List.append_assoc] at hpq_out
    have hq : q = [] := by
      subst hp
      simp [List.append_assoc] at hpq_out
      cases q with
      | nil => rfl
      | cons _ _ =>
        cases r.output <;> simp at hpq_out
    have hro : r.output = [] := by
      subst hp
      subst hq
      simpa using hpq_out
    have hcnf_r := hcnf r hr_mem
    obtain ⟨_, _, _, _, ho⟩ | ⟨_, ho⟩ | ⟨hinp, _⟩ := hcnf_r
    · simp [ho] at hro
    · simp [ho] at hro
    ·
      subst hp
      subst hq
      simp at hpq_in
      rw [hinp] at hpq_in
      have : ∀ sf, g.Derives [Symbol.nonterminal B] sf →
        Symbol.nonterminal g.initial ∉ sf := by
        intro sf hder
        induction hder with
        | refl => simp; exact fun h => hB h.symm
        | tail _ hlast ih_inner =>
          intro hmem
          obtain ⟨r', hr'_mem, hrw'⟩ := hlast
          obtain ⟨p', q', hp'_in, hp'_out⟩ := hrw'.exists_parts
          rw [hp'_out] at hmem
          simp [List.mem_append] at hmem
          obtain hmem_p | hmem_out | hmem_q := hmem
          · exact ih_inner (by rw [hp'_in]; exact List.mem_append_left _ (List.mem_append_left _ hmem_p))
          ·
            have hcnf_r' := hcnf r' hr'_mem
            obtain ⟨B'', C'', hB''ne, hC''ne, ho'⟩ | ⟨a', ho'⟩ | ⟨_, ho'⟩ := hcnf_r'
            · rw [ho'] at hmem_out; simp at hmem_out
              obtain h' | h' := hmem_out
              · exact hB''ne h'.symm
              · exact hC''ne h'.symm
            · rw [ho'] at hmem_out; simp at hmem_out
            · rw [ho'] at hmem_out; simp at hmem_out
          · exact ih_inner (by rw [hp'_in]; exact List.mem_append_right _ hmem_q)
      have h_not_mem := this _ hderiv_u
      rw [hpq_in] at h_not_mem
      exact h_not_mem (List.mem_singleton.mpr rfl)

end CFLPumping

namespace CFLPumping

/--
[cnf_tree_of_derives_aux](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_tree_of_derives_aux
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
-- given
  (hcnf : ChomskyNormalForm.IsCNF g) :
-- imply
  ∀ (n : ℕ) (A : g.NT) (w : List T), w.length ≤ n → w ≠ [] → g.Derives [Symbol.nonterminal A] (w.map Symbol.terminal) → ∃ (t : CNFParseTree g A), t.yield = w := by
-- proof
  intro n
  induction n with
  | zero =>
    intro A w hw hne _
    exfalso; exact hne (List.eq_nil_of_length_eq_zero (Nat.le_zero.mp hw))
  | succ n ih =>
  intro A w hw hne hd
  obtain ⟨v, hprod, hrest⟩ := derives_from_nt_nontrivial hne hd
  obtain ⟨r, hr_mem, hr_input, hv_eq⟩ := produces_from_singleton_nonterminal' hprod
  subst hv_eq
  have hcnf_r := hcnf r hr_mem
  obtain ⟨B, C, hBne, hCne, hr_out⟩ | ⟨a, hr_out⟩ | ⟨hinp, hr_out⟩ := hcnf_r
  ·
    rw [hr_out] at hrest
    have hsplit := derives_append_split
      (u := [Symbol.nonterminal B]) (v := [Symbol.nonterminal C]) hrest
    obtain ⟨w1, w2, heq, hd1, hd2⟩ := hsplit
    obtain ⟨s1, s2, hw1, hw2, hweq⟩ := map_terminal_split w w1 w2 heq
    rw [hw1] at hd1; rw [hw2] at hd2
    have hs1_ne : s1 ≠ [] := by
      intro hs1; subst hs1; simp at hd1
      exact cnf_nonempty_of_derives_ne_initial hcnf hBne _ hd1 rfl
    have hs2_ne : s2 ≠ [] := by
      intro hs2; subst hs2; simp at hd2
      exact cnf_nonempty_of_derives_ne_initial hcnf hCne _ hd2 rfl
    have hs1_len : s1.length ≤ n := by
      have : s2.length > 0 := List.length_pos_of_ne_nil hs2_ne
      rw [hweq] at hw; simp [List.length_append] at hw; omega
    have hs2_len : s2.length ≤ n := by
      have : s1.length > 0 := List.length_pos_of_ne_nil hs1_ne
      rw [hweq] at hw; simp [List.length_append] at hw; omega
    obtain ⟨t1, ht1⟩ := ih B s1 hs1_len hs1_ne hd1
    obtain ⟨t2, ht2⟩ := ih C s2 hs2_len hs2_ne hd2
    have hr_mem' : (⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ : ContextFreeRule T g.NT) ∈ g.rules := by
      have heq_r : r = ⟨A, [Symbol.nonterminal B, Symbol.nonterminal C]⟩ := by
        cases r; simp_all
      rw [← heq_r]; exact hr_mem
    exact ⟨.node A B C hr_mem' t1 t2, by simp [CNFParseTree.yield, ht1, ht2, hweq]⟩
  ·
    rw [hr_out] at hrest
    obtain h | ⟨v', hprod', _⟩ := hrest.eq_or_head
    ·
      have hw_eq : w = [a] := by
        have hlen : w.length = 1 := by
          have := congr_arg List.length h
          simp at this; exact this.symm
        match w, hlen with
        | [x], _ =>
          simp at h; exact congrArg ([·]) h.symm
      subst hw_eq
      have hr_mem' : (⟨A, [Symbol.terminal a]⟩ : ContextFreeRule T g.NT) ∈ g.rules := by
        have : r = ⟨A, [Symbol.terminal a]⟩ := by
          have h1 : r.input = A := hr_input
          have h2 : r.output = [Symbol.terminal a] := hr_out
          exact ContextFreeRule.ext h1 h2
        rw [← this]; exact hr_mem
      exact ⟨.leaf A a hr_mem', by simp [CNFParseTree.yield]⟩
    ·
      exfalso
      exact all_terminals_not_produces (w := [a]) hprod'
  ·
    rw [hr_out] at hrest
    exfalso
    have h := derives_nil_of_nil hrest
    exact hne (by cases w <;> simp_all)

end CFLPumping

namespace CFLPumping

/--
[cnf_tree_of_mem_language](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_tree_of_mem_language
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  {s : List T}
-- given
  (hcnf : ChomskyNormalForm.IsCNF g)
  (hs : s ∈ g.language)
  (hne : s ≠ []) :
-- imply
  ∃ (t : CNFParseTree g g.initial), t.yield = s := by
-- proof
  rw [ContextFreeGrammar.mem_language_iff] at hs
  exact cnf_tree_of_derives_aux g hcnf s.length g.initial s (Nat.le_refl _) hne hs

end CFLPumping

namespace CFLPumping

/--
[listPow_map](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma listPow_map
  {g : ContextFreeGrammar T}
  {f : α → β}
  {l : List α} :
-- imply
  ∀ n, (listPow l n).map f = listPow (l.map f) n := by
-- proof
  intro n; induction n with
  | zero => simp [listPow]
  | succ n ih => simp [listPow, List.map_append, ih]

end CFLPumping

namespace CFLPumping

/--
[tree_pump](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma tree_pump
  {g : ContextFreeGrammar T}
  {g : ContextFreeGrammar T}
  [Fintype g.NT]
  [DecidableEq g.NT]
  {A : g.NT}
  {t : CNFParseTree g A}
-- given
  (hh : t.height > Fintype.card g.NT) :
-- imply
  ∃ u v x y z : List T, t.yield = u ++ v ++ x ++ y ++ z ∧ (∀ i : ℕ, g.Derives [Symbol.nonterminal A] ((u ++ listPow v i ++ x ++ listPow y i ++ z).map Symbol.terminal)) ∧ (v ++ y).length > 0 ∧ (v ++ x ++ y).length ≤ 2 ^ (Fintype.card g.NT + 1) := by
-- proof
  set k := Fintype.card g.NT
  have hbase : t.height - k ≥ 1 := by omega
  let f : Fin (k + 1) → g.NT := fun i => t.ntAtDepth (t.height - k + i.val) (by omega)
  obtain ⟨i, j, hij, hfij⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt f (by rw [Fintype.card_fin]; omega)
  obtain ⟨d1f, d2f, hd12, hfd⟩ : ∃ d1 d2 : Fin (k + 1), d1 < d2 ∧ f d1 = f d2 := by
    obtain h | h := lt_or_gt_of_ne hij
    · exact ⟨i, j, h, hfij⟩
    · exact ⟨j, i, h, hfij.symm⟩
  set d1 := t.height - k + d1f.val
  set d2 := t.height - k + d2f.val
  have hd1_pos : 0 < d1 := by omega
  have hd1_le : d1 ≤ t.height := by omega
  have hd1_lt_d2 : d1 < d2 := by omega
  have hd_diff_pos : 0 < d2 - d1 := by omega
  have hnt_eq : t.ntAtDepth d1 hd1_le = t.ntAtDepth d2 (by omega) := by
    show f d1f = f d2f; exact hfd
  have hd12_le : d1 + (d2 - d1) ≤ t.height := by omega
  obtain ⟨R, sub, u_part, z_part, hR, hsub_h, hyield_outer, hderives_outer, hcoh⟩ :=
    t.exists_decomp_with_coherence d1 (d2 - d1) hd1_le hd12_le
  have hsub_nt : sub.ntAtDepth (d2 - d1) (by rw [hsub_h]; omega) = R := by
    rw [hcoh (by rw [hsub_h]; omega)]
    calc t.ntAtDepth (d1 + (d2 - d1)) hd12_le
      = t.ntAtDepth d2 (by omega) := by congr 1; omega
      _ = t.ntAtDepth d1 hd1_le := hnt_eq.symm
      _ = R := hR.symm
  obtain ⟨R', sub_inner, v_part, y_part, hR', hsub_inner_h, hyield_inner, hderives_inner, hctx⟩ :=
    sub.exists_decomp_nonempty_ctx (d2 - d1) (by rw [hsub_h]; omega) hd_diff_pos
  have hR'_eq_R : R' = R := by rw [hR', hsub_nt]
  subst hR'_eq_R
  refine ⟨u_part, v_part, sub_inner.yield, y_part, z_part, ?_, ?_, ?_, ?_⟩
  ·
    simp only [hyield_outer, hyield_inner, List.append_assoc]
  ·
    intro i
    have hpump := derives_pump_iter hderives_inner sub_inner.tree_derives i
    have hfull := hderives_outer.trans
      ((hpump.append_left (u_part.map Symbol.terminal)).append_right (z_part.map Symbol.terminal))
    simp only [List.map_append, List.append_assoc, listPow_map] at hfull ⊢
    exact hfull
  ·
    exact hctx
  ·
    have hsub_height_le : sub.height ≤ k + 1 := by rw [hsub_h]; omega
    have hyield_len := sub.yield_length_le_pow_height
    rw [hyield_inner] at hyield_len
    simp only [List.length_append] at hyield_len ⊢
    calc v_part.length + sub_inner.yield.length + y_part.length
      ≤ 2 ^ sub.height := hyield_len
      _ ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by omega) hsub_height_le

end CFLPumping

namespace CFLPumping

/--
[cnf_pumping_core](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ContextFree.lean)
-/
@[path]
lemma cnf_pumping_core
  {g : ContextFreeGrammar T}
  [Fintype g.NT]
  [DecidableEq g.NT]
  {s : List T}
-- given
  (hcnf : ChomskyNormalForm.IsCNF g)
  (hs : s ∈ g.language)
  (hlen : s.length ≥ 2 ^ (Fintype.card g.NT + 1)) :
-- imply
  ∃ u v x y z : List T, s = u ++ v ++ x ++ y ++ z ∧ (∀ i : ℕ, (u ++ listPow v i ++ x ++ listPow y i ++ z) ∈ g.language) ∧ (v ++ y).length > 0 ∧ (v ++ x ++ y).length ≤ 2 ^ (Fintype.card g.NT + 1) := by
-- proof
  have hne : s ≠ [] := by
    intro h; subst h; simp at hlen
  obtain ⟨t, ht⟩ := cnf_tree_of_mem_language g hcnf s hs hne
  have hheight : t.height > Fintype.card g.NT := by
    by_contra h
    push_neg at h
    have h1 := t.yield_length_le_pow_height
    rw [ht] at h1
    have h2 : 2 ^ t.height ≤ 2 ^ Fintype.card g.NT :=
      Nat.pow_le_pow_right (by omega) h
    have : 2 ^ Fintype.card g.NT < 2 ^ (Fintype.card g.NT + 1) :=
      Nat.pow_lt_pow_right (by omega) (by omega)
    omega
  obtain ⟨u, v, x, y, z, hyield, hpump, hvy, hvxy⟩ := tree_pump g t hheight
  exact ⟨u, v, x, y, z, ht ▸ hyield, fun i => by
    rw [ContextFreeGrammar.mem_language_iff]; exact hpump i, hvy, hvxy⟩
/-- **Pumping Lemma for Context Free Languages** (Sipser, Lecture 5).
For every CFL `A` there exists a *pumping length* `p ∈ ℕ` such that every string
`s ∈ A` with `|s| ≥ p` admits a decomposition `s = uvxyz` satisfying:
1. `u v^i x y^i z ∈ A` for all `i ≥ 0`,
2. `vy ≠ ε`, and
3. `|vxy| ≤ p`.
Proof: pick a CFG for `A`, convert it to a CNF grammar `g` with a finite
nonterminal type via `ChomskyNormalForm.cfg_to_cnf_fintype`, and apply
`cnf_pumping_core` with `p = 2^(|V|+1)`. -/

end CFLPumping


-- created on 2026-10-23
-- updated on 2026-10-28
