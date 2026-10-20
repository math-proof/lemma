import Mathlib
import sympy.Basic
import sympy.series.formal.WeightedSets
open scoped BigOperators
open PowerSeries Finset
open WeightedSet


/--
[weight_gen_fun_disjoint_union_eq](https://github.com/facebookresearch/algebraic-combinatorics/blob/main/AlgebraicCombinatorics/WeightedSets.lean)
-/
@[path]
private lemma main
  [CommSemiring R]
-- given
  {α β : Type*}
  (W₁ : WeightedSet α)
  (W₂ : WeightedSet β)
  (hft₁ : W₁.IsFiniteType)
  (hft₂ : W₂.IsFiniteType) :
-- imply
  (disjointUnion W₁ W₂).weightGenFun (R := R) (disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂) =
    W₁.weightGenFun hft₁ + W₂.weightGenFun hft₂ := by
-- proof
  ext n
  simp only [weightGenFun, PowerSeries.coeff_mk, map_add, countOfWeight]
  -- Use ncard which is independent of the proof of finiteness
  have h1 := hft₁ n
  have h2 := hft₂ n
  have hft_union := disjointUnion_isFiniteType W₁ W₂ hft₁ hft₂ n
  -- Convert to ncard
  have eq1 : (h1.toFinset.card : R) = ({a : α | W₁.weight a = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h1]
  have eq2 : (h2.toFinset.card : R) = ({b : β | W₂.weight b = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ h2]
  have eq_union : (hft_union.toFinset.card : R) = ({x : α ⊕ β | (disjointUnion W₁ W₂).weight x = n}.ncard : R) := by
    rw [Set.ncard_eq_toFinset_card _ hft_union]
  rw [eq1, eq2, eq_union]
  -- Establish the set equality: elements of weight n in the disjoint union are
  -- either from W₁ or W₂
  have hset : {x : α ⊕ β | (disjointUnion W₁ W₂).weight x = n} =
              (Sum.inl (β := β)) '' {a : α | W₁.weight a = n} ∪ (Sum.inr (α := α)) '' {b : β | W₂.weight b = n} := by
    ext x
    simp only [disjointUnion, Set.mem_ofPred_eq, Set.mem_union, Set.mem_image]
    constructor
    · intro hx
      cases x with
      | inl a => left; exact ⟨a, hx, rfl⟩
      | inr b => right; exact ⟨b, hx, rfl⟩
    · intro hx
      rcases hx with ⟨a, ha, rfl⟩ | ⟨b, hb, rfl⟩
      · exact ha
      · exact hb
  -- The two images are disjoint (Sum.inl and Sum.inr have disjoint ranges)
  have hdisj : Disjoint ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n})
                        ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}) := by
    rw [Set.disjoint_iff]
    intro x ⟨⟨a, _, ha⟩, ⟨b, _, hb⟩⟩
    cases ha
    simp at hb
  have h1' : ((Sum.inl (β := β)) '' {a : α | W₁.weight a = n}).Finite := h1.image Sum.inl
  have h2' : ((Sum.inr (α := α)) '' {b : β | W₂.weight b = n}).Finite := h2.image Sum.inr
  -- The ncard of a disjoint union is the sum of ncards
  have ncard_eq : {x : α ⊕ β | (disjointUnion W₁ W₂).weight x = n}.ncard =
                  {a : α | W₁.weight a = n}.ncard + {b : β | W₂.weight b = n}.ncard := by
    rw [hset, Set.ncard_union_eq hdisj h1' h2']
    rw [Set.ncard_image_of_injective _ Sum.inl_injective]
    rw [Set.ncard_image_of_injective _ Sum.inr_injective]
  simp only [ncard_eq, Nat.cast_add]


-- created on 2026-10-20
