/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean -/

import Mathlib.GroupTheory.Index
open scoped Pointwise


/-! # G-harmonic tuples

Source: Murali Menon, "Two Questions on G-Harmonic Tuples"
(https://arxiv.org/abs/2608.15873v1, Definition span lines 33--37 of `main.tex`).
For a group `G`, a tuple `a : Fin n → ℕ` of positive integers is `G`-harmonic when
subgroups `U i` of exact index `a i` have left cosets `g i • (U i : Set G)` that
are pairwise disjoint. Since `Subgroup.index` is `0` for infinite index,
positivity plus exact index equality rules out infinite index. -/

/-- A tuple `a` is `G`-harmonic when each entry is positive and subgroups of
exactly those indices have pairwise disjoint left cosets. -/
def IsGHarmonic (G : Type*) [Group G] {n : ℕ} (a : Fin n → ℕ) : Prop :=
  (∀ i, 0 < a i) ∧
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
      (∀ i, (U i).index = a i) ∧
        Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))

