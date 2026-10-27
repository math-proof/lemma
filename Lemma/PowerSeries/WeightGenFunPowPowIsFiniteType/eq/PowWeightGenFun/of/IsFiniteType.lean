import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[weight_gen_fun_pow_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
  [CommSemiring R]
-- given
  {α : Type*}
  (W : WeightedSet α)
  (hft : W.IsFiniteType)
  (k : ℕ) :
-- imply
  (W.pow k).weightGenFun (R := R) (pow_isFiniteType W hft k) =
    (W.weightGenFun hft) ^ k := by
-- proof
  classical
  induction k with
  | zero =>
    simp only [pow_zero]
    ext n
    simp only [weightGenFun, countOfWeight, PowerSeries.coeff_mk, PowerSeries.coeff_one]
    split_ifs with hn
    · -- n = 0: Show that there's exactly one element of weight 0
      subst hn
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = 0} = Set.univ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_univ, iff_true]
        rfl
      have hFinset : (pow_isFiniteType W hft 0 0).toFinset = Finset.univ := by
        ext f
        simp only [Set.Finite.mem_toFinset, pow, heq, Set.mem_univ, Finset.mem_univ]
      rw [hFinset]
      have : Unique (Fin 0 → α) := Pi.uniqueOfIsEmpty fun _ => α
      simp
    · -- n ≠ 0: No function Fin 0 → α has weight n > 0
      have heq : {f : Fin 0 → α | ∑ i : Fin 0, W.weight (f i) = n} = ∅ := by
        ext f
        simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        have : ∑ i : Fin 0, W.weight (f i) = 0 := rfl
        omega
      have hFinset : (pow_isFiniteType W hft 0 n).toFinset = ∅ := by
        ext f
        rw [Set.Finite.mem_toFinset]
        simp only [pow, heq, Set.mem_empty_iff_false]
        simp
      rw [hFinset]
      simp
  | succ n ih =>
    have hiso : (W.pow (n + 1)) ≅ᵥ (W ×ᵥ (W.pow n)) := ⟨pow_succ_equiv W n⟩
    calc (W.pow (n + 1)).weightGenFun (R := R) (pow_isFiniteType W hft (n + 1))
        = (W ×ᵥ (W.pow n)).weightGenFun (prod_isFiniteType W (W.pow n) hft (pow_isFiniteType W hft n)) := by
          exact weightGenFun_eq_of_isomorphic _ _ _ _ hiso
      _ = W.weightGenFun hft * (W.pow n).weightGenFun (pow_isFiniteType W hft n) := by
          exact weightGenFun_prod _ _ _ _
      _ = W.weightGenFun hft * (W.weightGenFun hft) ^ n := by rw [ih]
      _ = (W.weightGenFun hft) ^ (n + 1) := by ring


-- created on 2026-10-20
