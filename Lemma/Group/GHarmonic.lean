import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.GHarmonic
open scoped Pointwise


/--
[IsGHarmonic.intro](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma IsGHarmonic_intro_eq
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {U : Fin n → Subgroup G}
  {g : Fin n → G}
-- given
  (hpos : ∀ i, 0 < a i)
  (hidx : ∀ i, (U i).index = a i)
  (hdisj : Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G))) :
-- imply
  IsGHarmonic G a := by
-- proof
  apply IsGHarmonic.intro hpos U g hidx hdisj

/--
[IsGHarmonic.pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma IsGHarmonic_pos_eq
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h : IsGHarmonic G a) :
-- imply
  0 < a i := by
-- proof
  apply IsGHarmonic.pos h i

/--
[IsGHarmonic.witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma IsGHarmonic_witnesses_eq
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
-- given
  (h : IsGHarmonic G a) :
-- imply
  ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
    (∀ i, (U i).index = a i) ∧
    Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) := by
-- proof
  apply IsGHarmonic.witnesses h

/--
[isGHarmonic_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma isGHarmonic_iff_eq
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ} :
-- imply
  IsGHarmonic G a ↔
    (∀ i, 0 < a i) ∧
    ∃ (U : Fin n → Subgroup G) (g : Fin n → G),
    (∀ i, (U i).index = a i) ∧
    Set.PairwiseDisjoint Set.univ (fun i => g i • (↑(U i) : Set G)) := by
-- proof
  apply isGHarmonic_iff a

/--
[isGHarmonic_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma isGHarmonic_empty_eq
  [Group G] :
-- imply
  IsGHarmonic G (n := by
-- proof
  apply isGHarmonic_empty

/--
[isGHarmonic_singleton_one](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma isGHarmonic_singleton_one_eq
  [Group G] :
-- imply
  IsGHarmonic G (n := by
-- proof
  apply isGHarmonic_singleton_one

/--
[not_isGHarmonic_of_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GHarmonic.lean)
-/
@[path]
private lemma not_isGHarmonic_of_zero_eq
  [Group G]
  {n : ℕ}
  {a : Fin n → ℕ}
  {i : Fin n}
-- given
  (h0 : a i = 0) :
-- imply
  ¬ IsGHarmonic G a := by
-- proof
  apply not_isGHarmonic_of_zero i h0


-- created on 2026-10-20
