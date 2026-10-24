import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TheoryOfComputation.code.ConfigReachability
open SpaceComplexity ConfigReachability


namespace ConfigReachability

/--
[branch_reachable_of_valid](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean)
-/
@[path]
lemma branch_reachable_of_valid
  {Q : Type}
  {Γ : Type}
  {M : NTM Q Γ}
  {w : List Γ}
  {branch : ℕ → TuringMachine.Config Q Γ}
  {k : ℕ}
-- given
  (hvalid : M.IsValidBranch w branch) :
-- imply
  Relation.ReflTransGen M.step (M.initConfig w) (branch k) := by
-- proof
  induction k with
  | zero => rw [hvalid.1]
  | succ n ih =>
    have htrans := hvalid.2 n
    by_cases hhalt : M.isHaltConfig (branch n)
    · rw [htrans.2 hhalt]; exact ih
    · exact ih.tail (htrans.1 hhalt)

end ConfigReachability

namespace ConfigReachability

/--
[exists_branch_of_reflTransGen](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean)
-/
@[path]
lemma exists_branch_of_reflTransGen
  {Q : Type}
  {Γ : Type}
  {M : NTM Q Γ}
  {a b : TuringMachine.Config Q Γ}
-- given
  (hreach : Relation.ReflTransGen M.step a b)
  (hhalt_b : M.isHaltConfig b) :
-- imply
  ∃ (branch : ℕ → TuringMachine.Config Q Γ) (k : ℕ), branch 0 = a ∧ (∀ n, (¬M.isHaltConfig (branch n) → M.step (branch n) (branch (n + 1))) ∧ (M.isHaltConfig (branch n) → branch (n + 1) = branch n)) ∧ branch k = b := by
-- proof
  induction hreach using Relation.ReflTransGen.head_induction_on with
  | refl =>
    exact ⟨fun _ => b, 0, rfl, fun _ => ⟨fun h => absurd hhalt_b h, fun _ => rfl⟩, rfl⟩
  | @head a c hab hcb ih =>
    obtain ⟨branch', k', hstart', htrans', htarget'⟩ := ih
    refine ⟨fun n => match n with | 0 => a | n + 1 => branch' n, k' + 1, rfl, ?_, ?_⟩
    · intro n
      match n with
      | 0 =>
        constructor
        · intro _
          show M.step a (branch' 0)
          rw [hstart']; exact hab
        · intro hhalt_a
          exact absurd hhalt_a hab.1
      | n + 1 => exact htrans' n
    · show branch' k' = b
      exact htarget'

end ConfigReachability

namespace ConfigReachability

/--
[accepts_of_reflTransGen_accept](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean)
-/
@[path]
lemma accepts_of_reflTransGen_accept
  {Q : Type}
  {Γ : Type}
  {M : NTM Q Γ}
  {w : List Γ}
  {c : TuringMachine.Config Q Γ}
-- given
  (hreach : Relation.ReflTransGen M.step (M.initConfig w) c)
  (haccept : M.isAcceptConfig c) :
-- imply
  M.accepts w := by
-- proof
  have hhalt : M.isHaltConfig c := Or.inl haccept
  obtain ⟨branch, k, hstart, htrans, htarget⟩ :=
    exists_branch_of_reflTransGen M hreach hhalt
  exact ⟨branch, k, ⟨hstart, htrans⟩, htarget ▸ haccept⟩

end ConfigReachability

namespace ConfigReachability

/--
[accepts_iff_configGraph_reachable](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/ConfigReachability.lean)
-/
@[path]
lemma accepts_iff_configGraph_reachable
  {Q : Type}
  {Γ : Type}
  {M : NTM Q Γ}
  {w : List Γ} :
-- imply
  M.accepts w ↔ ∃ c, M.isAcceptConfig c ∧ (mkConfigGraph M w).Reachable (M.initConfig w) c := by
-- proof
  constructor
  ·
    rintro ⟨branch, k, hvalid, haccept⟩
    exact ⟨branch k, haccept, branch_reachable_of_valid M w branch hvalid k⟩
  ·
    rintro ⟨c, haccept, hreach⟩
    exact accepts_of_reflTransGen_accept M w hreach haccept

end ConfigReachability


-- created on 2026-10-23
