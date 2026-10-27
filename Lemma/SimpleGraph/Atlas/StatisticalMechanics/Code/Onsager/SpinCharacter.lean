import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SpinCharacter.Part2
open StatMech StatMech.Onsager


/--
[ons_homologyIntersection_add_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_homologyIntersection_add_right_eq
-- given
  (h k l : Fin 2 × Fin 2) :
-- imply
  ons_homologyIntersection h (k + l) = ons_homologyIntersection h k + ons_homologyIntersection h l := by
-- proof
  apply StatMech.Onsager.ons_homologyIntersection_add_right h k l

/--
[ons_homologyIntersection_sum_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_homologyIntersection_sum_right_eq
  {S : Finset iota}
  {f : iota → Fin 2 × Fin 2}
-- given
  (h : Fin 2 × Fin 2) :
-- imply
  ons_homologyIntersection h (∑ i ∈ S, f i) = ∑ i ∈ S, ons_homologyIntersection h (f i) := by
-- proof
  apply StatMech.Onsager.ons_homologyIntersection_sum_right h S f

/--
[ons_spinCharacter_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacter_add_eq
  {a b : Fin 2}
-- given
  (h k : Fin 2 × Fin 2) :
-- imply
  ons_spinCharacter a b (h + k) = ons_spinCharacter a b h * ons_spinCharacter a b k * (-1 : ℝ) ^ (ons_homologyIntersection h k).val := by
-- proof
  apply StatMech.Onsager.ons_spinCharacter_add a b h k

/--
[ons_spinCharacter_add_of_intersection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacter_add_of_intersection_zero_eq
  {a b : Fin 2}
-- given
  (h k : Fin 2 × Fin 2)
  (hzero : ons_homologyIntersection h k = 0) :
-- imply
  ons_spinCharacter a b (h + k) = ons_spinCharacter a b h * ons_spinCharacter a b k := by
-- proof
  apply StatMech.Onsager.ons_spinCharacter_add_of_intersection_zero a b h k hzero

/--
[ons_spinCharacter_sum_of_pairwise_intersection_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacter_sum_of_pairwise_intersection_zero_eq
  {a b : Fin 2}
  {S : Finset iota}
  {f : iota → Fin 2 × Fin 2}
-- given
  (hpair : ∀ i ∈ S, ∀ j ∈ S, i ≠ j → ons_homologyIntersection (f i) (f j) = 0) :
-- imply
  ons_spinCharacter a b (∑ i ∈ S, f i) = ∏ i ∈ S, ons_spinCharacter a b (f i) := by
-- proof
  apply StatMech.Onsager.ons_spinCharacter_sum_of_pairwise_intersection_zero a b S f hpair

/--
[ons_spinCharacterSum_eq_sector_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacterSum_eq_sector_sum_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ}
  {a b : Fin 2} :
-- imply
  ons_spinCharacterSum L x a b = ∑ h : Fin 2 × Fin 2, ons_spinCharacter a b h * ons_sectorWeight L x h := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_eq_sector_sum L x a b

/--
[ons_spinCharacterSum_zero_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacterSum_zero_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_spinCharacterSum L x 0 0 = ons_spin11 L x := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_zero_zero L x

/--
[ons_spinCharacterSum_one_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacterSum_one_zero_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_spinCharacterSum L x 1 0 = ons_spin01 L x := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_one_zero L x

/--
[ons_spinCharacterSum_zero_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacterSum_zero_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_spinCharacterSum L x 0 1 = ons_spin10 L x := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_zero_one L x

/--
[ons_spinCharacterSum_one_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SpinCharacter.lean)
-/
@[path]
private lemma ons_spinCharacterSum_one_one_eq
  {L : ℕ}
  [Fact (2 < L)]
  {x : ℝ} :
-- imply
  ons_spinCharacterSum L x 1 1 = ons_spin00 L x := by
-- proof
  apply StatMech.Onsager.ons_spinCharacterSum_one_one L x


-- created on 2026-10-23
