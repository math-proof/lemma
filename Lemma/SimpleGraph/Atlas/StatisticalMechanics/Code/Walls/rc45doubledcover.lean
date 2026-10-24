import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.rc45doubledcover
open Finset StatMech StatMech.Walls


/--
[rc45_slab1_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_slab1_card_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  (rc44_slab1 a 𝒜).card = (𝒜.filter (fun S => a ∈ S)).card := by
-- proof
  apply StatMech.Walls.rc45_slab1_card a 𝒜

/--
[rc45_slab_card_partition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_slab_card_partition_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)} :
-- imply
  𝒜.card = (rc44_slab0 a 𝒜).card + (rc44_slab1 a 𝒜).card := by
-- proof
  apply StatMech.Walls.rc45_slab_card_partition a 𝒜

/--
[rc45_famCylBoxE_card_diagonal_ub](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_famCylBoxE_card_diagonal_ub_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  (rc44_famCylBoxE E 𝒜 ℬ).card ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card := by
-- proof
  apply StatMech.Walls.rc45_famCylBoxE_card_diagonal_ub E a 𝒜 ℬ

/--
[rc45_reflInterE_card_antidiagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_reflInterE_card_antidiagonal_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (haE : a ∈ E) :
-- imply
  (rc44_reflInterE E 𝒜 ℬ).card = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card := by
-- proof
  apply StatMech.Walls.rc45_reflInterE_card_antidiagonal E a haE 𝒜 ℬ

/--
[rc45_diagonalBox_exceeds_reflInter_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_diagonalBox_exceeds_reflInter_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card < (rc44_famCylBoxEComp {0, 1} (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card + (rc44_famCylBoxEComp {0, 1} (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card := by
-- proof
  apply StatMech.Walls.rc45_diagonalBox_exceeds_reflInter_fin3

/--
[rc45_reflInterE_slabSwap_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_reflInterE_slabSwap_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card := by
-- proof
  apply StatMech.Walls.rc45_reflInterE_slabSwap_fails_fin3

/--
[rc45_reimer_closes_of_boxMonoResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_reimer_closes_of_boxMonoResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc44_BoxMonoResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc45_reimer_closes_of_boxMonoResidue h

/--
[rc45_boxMonoResidue_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_boxMonoResidue_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc45_boxMonoResidue_fin2 𝒜 ℬ

/--
[rc45_reimer_doubledcover](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc45doubledcover.lean)
-/
@[path]
private lemma rc45_reimer_doubledcover_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)), (rc44_famCylBoxE E 𝒜 ℬ).card ≤ (rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)).card + (rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)).card) ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)), (rc44_reflInterE E 𝒜 ℬ).card = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card) ∧ ((rc44_reflInterEComp (Finset.univ : Finset (Fin 3)) rc45_Astep rc45_Bstep).card < (rc44_famCylBoxEComp {0, 1} (rc44_slab0 2 rc45_Astep) (rc44_slab0 2 rc45_Bstep)).card + (rc44_famCylBoxEComp {0, 1} (rc44_slab1 2 rc45_Astep) (rc44_slab1 2 rc45_Bstep)).card) ∧ ((rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card < (rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc45_Aswap) (rc44_slab0 2 rc45_Bswap)).card + (rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc45_Aswap) (rc44_slab1 2 rc45_Bswap)).card) ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter) := by
-- proof
  apply StatMech.Walls.rc45_reimer_doubledcover


-- created on 2026-10-23
