import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.ExchangeConditionGenuine
open Finset BigOperators CoxeterExchangeGenuine


namespace Definitions
end Definitions
namespace CoxeterExchangeGenuine

/--
[exchange_from_bridge](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean)
-/
@[path]
private lemma exchange_from_bridge
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {bridge : GeometricBridgeHyp M cs} :
-- imply
  CoxeterExchange.SatisfiesExchangeCondition M cs := by
-- proof
  intro word s hred hlen
  exact bridge.sign_change_exchange word s hred
    (bridge.length_decrease_negative word s hred hlen)

end CoxeterExchangeGenuine

/--
[bilinForm_neg_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean)
-/
@[path]
private lemma bilinForm_neg_left
  [DecidableEq B]
  [Fintype B]
  {M : CoxeterMatrix B}
  {v w : B → ℝ} :
-- imply
  CoxeterGroup.bilinForm M (-v) w = -CoxeterGroup.bilinForm M v w := by
-- proof
  have : -v = (-1 : ℝ) • v := by ext x; simp
  rw [this, CoxeterGroup.bilinForm_smul_left]
  ring


namespace CoxeterExchangeGenuine

/--
[e_self_coord_positive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean)
-/
@[path]
private lemma e_self_coord_positive
  [DecidableEq B]
  [Fintype B]
  {s : B} :
-- imply
  CoxeterGroup.e s s > 0 := by
-- proof
  simp [CoxeterGroup.e]

end CoxeterExchangeGenuine

namespace CoxeterExchangeGenuine

/--
[exists_sign_change](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean)
-/
@[path]
private lemma exists_sign_change
  [DecidableEq B]
  [Fintype B]
  {f : ℕ → ℝ}
  {n : ℕ}
-- given
  (_hn : 0 < n)
  (hf0 : f 0 > 0)
  (hfn : f n < 0) :
-- imply
  ∃ k, k < n ∧ f k ≥ 0 ∧ f (k + 1) < 0 := by
-- proof
  by_contra h
  push_neg at h
  have : ∀ k, k ≤ n → f k ≥ 0 := by
    intro k hk
    induction k with
    | zero => linarith
    | succ m ih =>
      have hm_le : m ≤ n := by omega
      have hm_lt : m < n := by omega
      exact h m hm_lt (ih hm_le)
  linarith [this n le_rfl]

end CoxeterExchangeGenuine

namespace CoxeterExchangeGenuine

/--
[exists_sign_change'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/ExchangeConditionGenuine.lean)
-/
@[path]
private lemma exists_sign_change'
  [DecidableEq B]
  [Fintype B]
  {f : ℕ → ℝ}
  {n : ℕ}
-- given
  (_hn : 0 < n)
  (hf0 : f 0 > 0)
  (hfn : f n ≤ 0) :
-- imply
  ∃ k, k < n ∧ f k > 0 ∧ f (k + 1) ≤ 0 := by
-- proof
  by_contra h
  push_neg at h
  have : ∀ k, k ≤ n → f k > 0 := by
    intro k hk
    induction k with
    | zero => exact hf0
    | succ m ih =>
      have hm_le : m ≤ n := by omega
      have hm_lt : m < n := by omega
      exact h m hm_lt (ih hm_le)
  linarith [this n le_rfl]

end CoxeterExchangeGenuine


-- created on 2026-10-24
