import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.ArtinGroup
open CoxeterMatrix
open ArtinGroup


/--
[alternatingWord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma alternatingWord_zero_eq
  [Monoid G]
  {a b : G} :
-- imply
  alternatingWord a b 0 = 1 := by
-- proof
  apply CoxeterMatrix.alternatingWord_zero a b

/--
[alternatingWord_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma alternatingWord_succ_eq
  [Monoid G]
  {a b : G}
  {n : ℕ} :
-- imply
  alternatingWord a b (n + 1) = a * alternatingWord b a n := by
-- proof
  apply CoxeterMatrix.alternatingWord_succ a b n

/--
[map_alternatingWord](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma map_alternatingWord_eq
  [Monoid G] [Monoid H]
  {f : G →* H}
  {a b : G}
  {n : ℕ} :
-- imply
  f (alternatingWord a b n) = alternatingWord (f a) (f b) n := by
-- proof
  apply CoxeterMatrix.map_alternatingWord f a b n

/--
[closure_range_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma closure_range_of_eq
  {M : CoxeterMatrix B} :
-- imply
  Subgroup.closure (Set.range (of M)) = ⊤ := by
-- proof
  apply CoxeterMatrix.ArtinGroup.closure_range_of M

/--
[braid_relation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma braid_relation_eq
  {M : CoxeterMatrix B}
  {i j : B}
-- given
  (hij : i ≠ j)
  (h : M i j ≠ 0) :
-- imply
  alternatingWord (of M i) (of M j) (M i j) = alternatingWord (of M j) (of M i) (M i j) := by
-- proof
  apply CoxeterMatrix.ArtinGroup.braid_relation M hij h


-- created on 2026-10-20
