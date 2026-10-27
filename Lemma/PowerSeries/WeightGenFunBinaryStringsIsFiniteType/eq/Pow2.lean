import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.Combinatorics.Enumerative.WeightedSets.Part26
import Lemma.PowerSeries.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet WeightedSetExamples


private lemma binaryStrings_countOfWeight (n : ℕ) :
    BinaryStrings.countOfWeight binaryStrings_isFiniteType n = 2 ^ n := by
  unfold WeightedSet.countOfWeight
  have h_eq : {a : List (Fin 2) | BinaryStrings.weight a = n} =
              Set.range (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    ext l
    simp only [Set.mem_ofPred_eq, Set.mem_range, BinaryStrings]
    constructor
    · intro hl; exact ⟨⟨l, hl⟩, rfl⟩
    · intro ⟨v, hv⟩; rw [← hv]; exact v.toList_length
  have h_inj : Function.Injective (List.Vector.toList : List.Vector (Fin 2) n → List (Fin 2)) := by
    intro v w h
    exact List.Vector.toList_injective h
  have h_finite := binaryStrings_isFiniteType n
  have h_card : h_finite.toFinset.card = {a : List (Fin 2) | BinaryStrings.weight a = n}.ncard := by
    rw [Set.ncard]
    simp only [h_finite.encard_eq_coe_toFinset_card, ENat.toNat_natCast]
  rw [h_card, h_eq]
  rw [Set.ncard_range_of_injective h_inj]
  rw [Nat.card_eq_fintype_card]
  rw [Fintype.ofEquiv_card (Equiv.vectorEquivFin (Fin 2) n).symm]
  simp [Fintype.card_fin]


/--
[weight_gen_fun_binary_strings_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main :
-- imply
  BinaryStrings.weightGenFun (R := ℚ) binaryStrings_isFiniteType =
    PowerSeries.mk fun n => (2 ^ n : ℚ) := by
-- proof
  ext n
  simp only [WeightedSet.weightGenFun, PowerSeries.coeff_mk]
  rw [binaryStrings_countOfWeight]
  simp


-- created on 2026-10-20
