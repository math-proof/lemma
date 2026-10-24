import Mathlib
import sympy.Basic


namespace Lagrange

/--
[card_eq_index_mul_card](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Lagrange.lean)
-/
@[path]
private lemma card_eq_index_mul_card
  [Group G]
  [Fintype G]
  {H : Subgroup G} [Fintype H] :
-- imply
  Fintype.card G = H.index * Fintype.card H := by
-- proof
  have h := Subgroup.index_mul_card H
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, eq_comm] at h

end Lagrange

namespace Lagrange

/--
[lagrange_dvd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Lagrange.lean)
-/
@[path]
private lemma lagrange_dvd
  [Group G]
  [Fintype G]
  {H : Subgroup G} [Fintype H] :
-- imply
  Fintype.card H ∣ Fintype.card G := by
-- proof
  have := H.card_subgroup_dvd_card
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

end Lagrange

namespace Lagrange

/--
[lagrange_theorem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Lagrange.lean)
-/
@[path]
private lemma lagrange_theorem
  [Group G]
  [Fintype G]
  {H : Subgroup G} [Fintype H] :
-- imply
  Fintype.card H ∣ Fintype.card G := by
-- proof
  have := Subgroup.card_subgroup_dvd_card H
  rwa [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at this

end Lagrange

namespace Lagrange

/--
[counting_formula](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraNotes/code/Lagrange.lean)
-/
@[path]
private lemma counting_formula
  [Group G]
  [Fintype G]
  {H : Subgroup G} [Fintype H] :
-- imply
  Fintype.card G = Fintype.card H * H.index := by
-- proof
  have h := H.card_mul_index
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card] at h
  omega

end Lagrange


-- created on 2026-10-24
