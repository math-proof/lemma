/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/GroupTheory/GHarmonic.lean -/


import sympy.atlas.GroupTheory.GHarmonic
import Lemma.Set.IsGHarmonicG.of.PairwiseDisjoint.All_EqIndex.All_Gt_0
import Mathlib.Algebra.Group.TypeTags.Finite

open scoped Pointwise


-- The empty tuple is `G`-harmonic.
example (G : Type*) [Group G] : IsGHarmonic G (n := 0) Fin.elim0 :=
  isGHarmonic_empty

-- A positive singleton is `G`-harmonic.
example (G : Type*) [Group G] : IsGHarmonic G (n := 1) (fun _ => 1) :=
  isGHarmonic_singleton_one

-- A singleton with a zero entry is rejected through positivity.
example (G : Type*) [Group G] : ¬ IsGHarmonic G (n := 1) (fun _ => 0) := by
  apply not_isGHarmonic_of_zero 0
  rfl

-- The positivity projection fires on the singleton witness.
example (G : Type*) [Group G] (h : IsGHarmonic G (n := 1) (fun _ => 1)) :
    0 < (fun _ => 1) (0 : Fin 1) :=
  h.pos 0

-- The witnesses projection exposes subgroups and representatives.
example (G : Type*) [Group G] (h : IsGHarmonic G (n := 1) (fun _ => 1)) :
    ∃ (U : Fin 1 → Subgroup G) (g : Fin 1 → G),
      (∀ i, (U i).index = (fun _ => 1) i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) :=
  h.witnesses

-- Two distinct cosets of `⊥` in `Multiplicative (Fin 2)` are disjoint.
example : IsGHarmonic (Multiplicative (Fin 2)) (n := 2) (fun _ => 2) := by
  refine IsGHarmonic.intro (fun _ => by decide) (fun _ => ⊥)
    (fun i => Multiplicative.ofAdd i) (fun i => ?_) ?_
  · rw [Subgroup.index_bot, Nat.card_eq_fintype_card,
      Fintype.card_multiplicative, Fintype.card_fin]
  · intro i _ j _ hij
    simp only [Subgroup.coe_bot, Set.smul_set_singleton, smul_eq_mul, mul_one]
    exact Set.disjoint_singleton.mpr hij
