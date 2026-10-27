import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc46butterfly.Part3
open Finset StatMech StatMech.Walls


/--
[rc46_famCylBoxDoubled_card_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_famCylBoxDoubled_card_eq_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc46_famCylBoxDoubled 𝒜 ℬ).card = (rc20_famCylBox 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc46_famCylBoxDoubled_card_eq 𝒜 ℬ

/--
[rc46_doubleCompress_card_any](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_doubleCompress_card_any_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 : Finset (Finset (α ⊕ α))} :
-- imply
  (doubleCompress i 𝒜).card = 𝒜.card := by
-- proof
  apply StatMech.Walls.rc46_doubleCompress_card_any i 𝒜

/--
[rc46_doubleCompress_famCylBoxDoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_doubleCompress_famCylBoxDoubled_card_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (doubleCompress i (rc46_famCylBoxDoubled 𝒜 ℬ)).card = (rc46_famCylBoxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc46_doubleCompress_famCylBoxDoubled_card i 𝒜 ℬ

/--
[rc46_doubleCompress_complBoxDoubled_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_doubleCompress_complBoxDoubled_card_eq
  [Fintype α]
  [DecidableEq α]
  {i : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ)).card = (rc37_complBoxDoubled 𝒜 ℬ).card := by
-- proof
  apply StatMech.Walls.rc46_doubleCompress_complBoxDoubled_card i 𝒜 ℬ

/--
[rc46_downDownStep_decreases_famCylBox_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_downDownStep_decreases_famCylBox_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_famCylBoxComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card < (rc20_famCylBoxComp 3 rc46_Adn rc46_Bdn).card := by
-- proof
  apply StatMech.Walls.rc46_downDownStep_decreases_famCylBox_fin3

/--
[rc46_downDownStep_reflInter_stable_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_downDownStep_reflInter_stable_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc20_reflInterComp 3 (Down.compression 1 rc46_Adn) (Down.compression 1 rc46_Bdn)).card = (rc20_reflInterComp 3 rc46_Adn rc46_Bdn).card := by
-- proof
  apply StatMech.Walls.rc46_downDownStep_reflInter_stable_fin3

/--
[rc46_dblEmpty02_not_complementary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_dblEmpty02_not_complementary_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ¬ rc46_isComplementary (dbl (∅ : Finset (Fin 3)) {0, 2}) := by
-- proof
  apply StatMech.Walls.rc46_dblEmpty02_not_complementary

/--
[rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  dbl (∅ : Finset (Fin 3)) {0, 2} ∈ doubleCompress 1 (rc37_complBoxDoubled rc46_Acf rc46_Bcf) := by
-- proof
  apply StatMech.Walls.rc46_dblEmpty02_mem_doubleCompress_complBoxDoubled

/--
[rc46_doubleCompress_breaks_complementary_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_doubleCompress_breaks_complementary_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ∃ (𝒜 ℬ : Finset (Finset (Fin 3))) (i : Fin 3) (U : Finset (Fin 3 ⊕ Fin 3)), U ∈ doubleCompress i (rc37_complBoxDoubled 𝒜 ℬ) ∧ ¬ rc46_isComplementary U := by
-- proof
  apply StatMech.Walls.rc46_doubleCompress_breaks_complementary_fin3

/--
[rc46_famCylBoxDoubled_le_at_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_famCylBoxDoubled_le_at_increasing_eq
  [Fintype α]
  [DecidableEq α]
  {n : ℕ}
  {A B : Set (ConfigSpace (Fin n))}
-- given
  (hA : IsIncreasing A)
  (hB : IsIncreasing B) :
-- imply
  (rc46_famCylBoxDoubled (eventFamily A) (eventFamily B)).card ≤ (rc37_complBoxDoubled (eventFamily A) (eventFamily B)).card := by
-- proof
  apply StatMech.Walls.rc46_famCylBoxDoubled_le_at_increasing hA hB

/--
[rc46_reimer_closes_of_boxMonoResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_reimer_closes_of_boxMonoResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc44_BoxMonoResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc46_reimer_closes_of_boxMonoResidue h

/--
[rc46_boxMonoResidue_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc46butterfly.lean)
-/
@[path]
private lemma rc46_boxMonoResidue_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc46_boxMonoResidue_fin2 𝒜 ℬ


-- created on 2026-10-23
