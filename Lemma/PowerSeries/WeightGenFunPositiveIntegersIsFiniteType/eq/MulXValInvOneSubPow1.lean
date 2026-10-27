import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


private lemma countOfWeight_zero : PositiveIntegers.countOfWeight positiveIntegers_isFiniteType 0 = 0 := by
  simp only [WeightedSet.countOfWeight]
  convert Finset.card_empty
  simp only [Set.Finite.toFinset_eq_empty]
  ext x
  simp only [PositiveIntegers, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
  exact x.2.ne'


private lemma countOfWeight_pos (n : ℕ) (hn : 0 < n) :
    PositiveIntegers.countOfWeight positiveIntegers_isFiniteType n = 1 := by
  unfold WeightedSet.countOfWeight
  let a : ℕ+ := ⟨n, hn⟩
  have hset : {x : ℕ+ | PositiveIntegers.weight x = n} = {a} := by
    ext x
    simp only [PositiveIntegers, Set.mem_ofPred_eq, a]
    exact ⟨fun hx => Subtype.ext hx, fun hx => hx ▸ rfl⟩
  have hfin : ({a} : Set ℕ+).Finite := Set.finite_singleton a
  have heq : (positiveIntegers_isFiniteType n).toFinset = hfin.toFinset :=
    Set.Finite.toFinset_inj.mpr hset
  rw [heq, Set.Finite.toFinset_singleton, Finset.card_singleton]


/--
[weight_gen_fun_positive_integers_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  PositiveIntegers.weightGenFun (R := ℚ) positiveIntegers_isFiniteType =
    PowerSeries.X * (PowerSeries.invOneSubPow ℚ 1).val := by
-- proof
  ext n
  simp only [WeightedSet.weightGenFun, coeff_mk]
  cases n with
  | zero =>
    simp [countOfWeight_zero, coeff_zero_X_mul]
  | succ n =>
    rw [coeff_succ_X_mul]
    rw [countOfWeight_pos (n + 1) (Nat.succ_pos n)]
    rw [show (1 : ℕ) = 0 + 1 from rfl, invOneSubPow_val_succ_eq_mk_add_choose]
    simp


-- created on 2026-10-20
