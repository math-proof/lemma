import Mathlib
import sympy.Basic
import sympy.atlas.GroupTheory.GroupGrowth
open Group.Generators


namespace Group.Generators

/--
[growth_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma growth_zero
  [Group G]
  {P : Group.Generators G ι} :
-- imply
  P.growth 0 = 1 := by
-- proof
  show Nat.card {g : G // P.wordLength g ≤ 0} = 1
  refine Nat.card_eq_one_iff_unique.mpr ⟨⟨fun a b => Subtype.ext ?_⟩, ⟨⟨1, by simp⟩⟩⟩
  rw [P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp a.2),
    P.wordLength_eq_zero_iff.mp (Nat.le_zero.mp b.2)]

end Group.Generators

namespace Group.Generators

/--
[growth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma growth_pos
  [Group G]
  {P : Group.Generators G ι}
  [Finite G]
  {n : ℕ} :
-- imply
  0 < P.growth n := by
-- proof
  show 0 < Nat.card {g : G // P.wordLength g ≤ n}
  have : Nonempty {g : G // P.wordLength g ≤ n} :=
    ⟨⟨1, by rw [P.wordLength_one]; exact Nat.zero_le n⟩⟩
  exact Nat.card_pos

end Group.Generators

namespace Group.Generators

/--
[growth_le_card](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma growth_le_card
  [Group G]
  {P : Group.Generators G ι}
  [Finite G]
  {n : ℕ} :
-- imply
  P.growth n ≤ Nat.card G := by
-- proof
  show Nat.card {g : G // P.wordLength g ≤ n} ≤ Nat.card G
  exact Finite.card_subtype_le _

end Group.Generators

namespace Group.Generators

/--
[hasPolynomialGrowth_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma hasPolynomialGrowth_of_finite
  [Group G] [Finite G]
  {P : Group.Generators G ι} :
-- imply
  P.HasPolynomialGrowth := by
-- proof
  refine ⟨fun _ => inferInstance, Nat.card G, 0, fun n => ?_⟩
  simpa using P.growth_le_card n

end Group.Generators

namespace Group.Generators

/--
[growth_pos_of_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma growth_pos_of_finite
  [Group G]
  {P : Group.Generators G ι}
  {n : ℕ}
-- given
  (hfin : ∀ n, Finite {g : G // P.wordLength g ≤ n}) :
-- imply
  0 < P.growth n := by
-- proof
  haveI := hfin n
  show 0 < Nat.card {g : G // P.wordLength g ≤ n}
  have : Nonempty {g : G // P.wordLength g ≤ n} :=
    ⟨⟨1, by rw [P.wordLength_one]; exact Nat.zero_le n⟩⟩
  exact Nat.card_pos

end Group.Generators

namespace Group.Generators

/--
[HasPolynomialGrowth.growth_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/GroupGrowth.lean)
-/
@[path]
lemma HasPolynomialGrowth.growth_pos
  [Group G]
  {P : Group.Generators G ι}
  {n : ℕ}
-- given
  (h : P.HasPolynomialGrowth) :
-- imply
  0 < P.growth n :=
-- proof
  P.growth_pos_of_finite h.1 n

end Group.Generators


-- created on 2026-10-20
-- updated on 2026-10-23
