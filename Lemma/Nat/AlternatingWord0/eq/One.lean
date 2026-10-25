import Mathlib
import sympy.Basic
import Def.GroupTheory.ArtinGroup.Part2
open CoxeterMatrix
open ArtinGroup


namespace Definitions
end Definitions
namespace CoxeterMatrix

/--
[alternatingWord_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma alternatingWord_zero
  [Monoid G]
  {a b : G} :
-- imply
  alternatingWord a b 0 = 1 :=
-- proof
  rfl

end CoxeterMatrix

namespace CoxeterMatrix

/--
[alternatingWord_succ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma alternatingWord_succ
  [Monoid G]
  {a b : G}
  {n : ℕ} :
-- imply
  alternatingWord a b (n + 1) = a * alternatingWord b a n :=
-- proof
  rfl

end CoxeterMatrix

namespace CoxeterMatrix

/--
[map_alternatingWord](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma map_alternatingWord
  [Monoid G] [Monoid H]
  {f : G →* H}
  {a b : G}
  {n : ℕ} :
-- imply
  f (alternatingWord a b n) = alternatingWord (f a) (f b) n := by
-- proof
  induction n generalizing a b with
  | zero => simp
  | succ n ih => simp [alternatingWord, ih]

end CoxeterMatrix

namespace CoxeterMatrix.ArtinGroup

/--
[closure_range_of](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma closure_range_of
  {M : CoxeterMatrix B} :
-- imply
  Subgroup.closure (Set.range (of M)) = ⊤ :=
-- proof
  PresentedGroup.closure_range_of _

end CoxeterMatrix.ArtinGroup

namespace CoxeterMatrix.ArtinGroup

/--
[braid_relation](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ArtinGroup.lean)
-/
@[path]
private lemma braid_relation
  {M : CoxeterMatrix B}
  {i j : B}
-- given
  (hij : i ≠ j)
  (h : M i j ≠ 0) :
-- imply
  alternatingWord (of M i) (of M j) (M i j) = alternatingWord (of M j) (of M i) (M i j) := by
-- proof
  have hmem : M.artinRelation i j ∈ M.artinRelationsSet := ⟨i, j, hij, h, rfl⟩
  have key := PresentedGroup.mk_eq_mk_of_mul_inv_mem hmem
  rwa [map_alternatingWord (PresentedGroup.mk _), map_alternatingWord (PresentedGroup.mk _)] at key

end CoxeterMatrix.ArtinGroup


-- created on 2026-10-20
-- updated on 2026-10-24
