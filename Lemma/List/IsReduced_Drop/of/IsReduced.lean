import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.CoxeterGroup.RootSignChangeProof
open Finset BigOperators CoxeterGroup CoxeterExchangeGenuine CoxeterRootSignChange


/--
[isReduced_drop](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/RootSignChangeProof.lean)
-/
@[path]
private lemma main
  [DecidableEq B]
  [Fintype B]
  [Group W]
  {M : CoxeterMatrix B}
  {cs : CoxeterSystem M W}
  {word : List B}
  {j : ℕ}
-- given
  (hred : cs.IsReduced word) :
-- imply
  cs.IsReduced (word.drop j) := by
-- proof
  unfold CoxeterSystem.IsReduced
  have htake := cs.length_wordProd_le (word.take j)
  have hdrop := cs.length_wordProd_le (word.drop j)
  have hprod : cs.wordProd word = cs.wordProd (word.take j) * cs.wordProd (word.drop j) := by
    rw [← CoxeterSystem.wordProd_append, List.take_append_drop]
  have hcat : cs.length (cs.wordProd word) ≤
    cs.length (cs.wordProd (word.take j)) + cs.length (cs.wordProd (word.drop j)) := by
    rw [hprod]; exact cs.length_mul_le _ _
  have hlen : word.length = (word.take j).length + (word.drop j).length := by
    rw [← List.length_append, List.take_append_drop]
  rw [hred] at hcat; omega


-- created on 2026-10-23
-- updated on 2026-10-26
