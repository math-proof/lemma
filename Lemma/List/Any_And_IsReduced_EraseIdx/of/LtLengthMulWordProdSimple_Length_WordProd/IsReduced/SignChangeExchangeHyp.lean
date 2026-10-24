import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.StrongExchangeBridge
open CoxeterExchange CoxeterGroup CoxeterExchangeGenuine StrongExchangeBridge


namespace StrongExchangeBridge

/--
[exchange_descent_eraseIdx](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeBridge.lean)
-/
@[path]
lemma exchange_descent_eraseIdx
  [Group W]
  [DecidableEq B]
  [Fintype B]
  {word : List B}
  {s : B}
-- given
  (hsce : SignChangeExchangeHyp M cs)
  (hred : cs.IsReduced word)
  (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
-- imply
  ∃ i : Fin word.length, cs.wordProd (word.eraseIdx i) = cs.wordProd word * cs.simple s ∧ cs.IsReduced (word.eraseIdx i) := by
-- proof
  have hex := exchange_condition_from_neg_of_descent M cs hsce
  obtain ⟨i, hi_eq⟩ := hex word s hred hdesc
  refine ⟨i, hi_eq, ?_⟩
  unfold CoxeterSystem.IsReduced
  rw [hi_eq]
  have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
    List.length_eraseIdx_of_lt i.isLt
  rw [hlen_erased]
  unfold CoxeterSystem.IsReduced at hred
  obtain h | h := cs.length_mul_simple (cs.wordProd word) s
  · omega
  · omega

end StrongExchangeBridge

/--
[exists_reduced_ending_in](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeBridge.lean)
-/
@[path]
lemma exists_reduced_ending_in
  [Group W]
  [DecidableEq B]
  [Fintype B]
  {word : List B}
  {s : B}
-- given
  (hsce : SignChangeExchangeHyp M cs)
  (hred : cs.IsReduced word)
  (hdesc : cs.length (cs.wordProd word * cs.simple s) < cs.length (cs.wordProd word)) :
-- imply
  ∃ (prefix_word : List B), cs.IsReduced (prefix_word ++ [s]) ∧ cs.wordProd (prefix_word ++ [s]) = cs.wordProd word ∧ prefix_word.length + 1 = word.length := by
-- proof
  have hex := exchange_condition_from_neg_of_descent M cs hsce
  obtain ⟨i, hi_eq⟩ := hex word s hred hdesc
  refine ⟨word.eraseIdx i, ?_, ?_, ?_⟩
  ·
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_append, cs.wordProd_singleton, hi_eq, mul_assoc,
      cs.simple_mul_simple_self, mul_one,
      List.length_append, List.length_singleton]
    have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
      List.length_eraseIdx_of_lt i.isLt
    rw [hlen_erased]
    unfold CoxeterSystem.IsReduced at hred
    omega
  ·
    rw [cs.wordProd_append, cs.wordProd_singleton, hi_eq, mul_assoc,
      cs.simple_mul_simple_self, mul_one]
  ·
    have hlen_erased : (word.eraseIdx ↑i).length = word.length - 1 :=
      List.length_eraseIdx_of_lt i.isLt
    rw [hlen_erased]
    have hword_pos : word.length > 0 := by
      unfold CoxeterSystem.IsReduced at hred; omega
    omega


namespace StrongExchangeBridge

/--
[exists_reduced_word_ending_in_descent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/StrongExchangeBridge.lean)
-/
@[path]
lemma exists_reduced_word_ending_in_descent
  [Group W]
  [DecidableEq B]
  [Fintype B]
  {w : W}
  {s : B}
-- given
  (hdesc : cs.length (w * cs.simple s) < cs.length w) :
-- imply
  ∃ (prefix_word : List B), cs.IsReduced (prefix_word ++ [s]) ∧ cs.wordProd (prefix_word ++ [s]) = w := by
-- proof
  obtain ⟨ω, hωred, hωprod⟩ := cs.exists_reduced_word (w * cs.simple s)
  have hωlen : ω.length = cs.length (w * cs.simple s) := by rw [hωprod]; exact hωred.symm
  refine ⟨ω, ?_, ?_⟩
  ·
    unfold CoxeterSystem.IsReduced
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hωprod, mul_assoc,
      cs.simple_mul_simple_self, mul_one,
      List.length_append, List.length_singleton]
    obtain h | h := cs.length_mul_simple w s
    · omega
    · omega
  ·
    rw [cs.wordProd_append, cs.wordProd_singleton, ← hωprod, mul_assoc,
      cs.simple_mul_simple_self, mul_one]

end StrongExchangeBridge


-- created on 2026-10-23
