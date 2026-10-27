import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc44boxineq.Part4
open Finset StatMech StatMech.Walls


/--
[rc44_mem_famCylBoxE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_mem_famCylBoxE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc44_famCylBoxE E 𝒜 ℬ ↔ S ⊆ E ∧ ∃ K L : Finset α, K ⊆ E ∧ L ⊆ E ∧ Disjoint K L ∧ (∀ T ⊆ E, T ∩ K = S ∩ K → T ∈ 𝒜) ∧ (∀ T ⊆ E, T ∩ L = S ∩ L → T ∈ ℬ) := by
-- proof
  apply StatMech.Walls.rc44_mem_famCylBoxE E 𝒜 ℬ S

/--
[rc44_mem_reflInterE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_mem_reflInterE_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)}
  {R : Finset α} :
-- imply
  R ∈ rc44_reflInterE E 𝒜 ℬ ↔ R ⊆ E ∧ R ∈ 𝒜 ∧ E \ R ∈ ℬ := by
-- proof
  apply StatMech.Walls.rc44_mem_reflInterE E 𝒜 ℬ R

/--
[rc44_famCylBoxE_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_famCylBoxE_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_famCylBoxE Finset.univ 𝒜 ℬ = rc20_famCylBox 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc44_famCylBoxE_univ 𝒜 ℬ

/--
[rc44_reflInterE_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reflInterE_univ_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_reflInterE Finset.univ 𝒜 ℬ = rc10_reflInter 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc44_reflInterE_univ 𝒜 ℬ

/--
[rc44_mem_slab0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_mem_slab0_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc44_slab0 a 𝒜 ↔ S ∈ 𝒜 ∧ a ∉ S := by
-- proof
  apply StatMech.Walls.rc44_mem_slab0 a 𝒜 S

/--
[rc44_mem_slab1](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_mem_slab1_eq
  [Fintype α]
  [DecidableEq α]
  {a : α}
  {𝒜 : Finset (Finset α)}
  {S : Finset α} :
-- imply
  S ∈ rc44_slab1 a 𝒜 ↔ ∃ U ∈ 𝒜, a ∈ U ∧ U.erase a = S := by
-- proof
  apply StatMech.Walls.rc44_mem_slab1 a 𝒜 S

/--
[rc44_inter_erase_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_inter_erase_of_not_mem_eq
  [Fintype α]
  [DecidableEq α]
  {T K : Finset α}
  {a : α}
-- given
  (ha : a ∉ T) :
-- imply
  T ∩ K.erase a = T ∩ K := by
-- proof
  apply StatMech.Walls.rc44_inter_erase_of_not_mem T K a ha

/--
[rc44_disjoint_erase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_disjoint_erase_eq
  [Fintype α]
  [DecidableEq α]
  {K L : Finset α}
  {a : α}
-- given
  (h : Disjoint K L) :
-- imply
  Disjoint (K.erase a) (L.erase a) := by
-- proof
  apply StatMech.Walls.rc44_disjoint_erase K L a h

/--
[rc44_slab0_famCylBoxE_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_slab0_famCylBoxE_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_slab0 a (rc44_famCylBoxE E 𝒜 ℬ) ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ) := by
-- proof
  apply StatMech.Walls.rc44_slab0_famCylBoxE_subset E a 𝒜 ℬ

/--
[rc44_inter_insert](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_inter_insert_eq
  [Fintype α]
  [DecidableEq α]
  {T' K U : Finset α}
  {a : α}
-- given
  (haU : a ∈ U)
  (htrace : T' ∩ K.erase a = U.erase a ∩ K.erase a) :
-- imply
  (insert a T') ∩ K = U ∩ K := by
-- proof
  apply StatMech.Walls.rc44_inter_insert T' K U a haU htrace

/--
[rc44_slab1_famCylBoxE_subset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_slab1_famCylBoxE_subset_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_slab1 a (rc44_famCylBoxE E 𝒜 ℬ) ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ) := by
-- proof
  apply StatMech.Walls.rc44_slab1_famCylBoxE_subset E a 𝒜 ℬ

/--
[rc44_sdiff_erase_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_sdiff_erase_of_not_mem_eq
  [Fintype α]
  [DecidableEq α]
  {E R : Finset α}
  {a : α} :
-- imply
  (E.erase a) \ R = (E \ R).erase a := by
-- proof
  apply StatMech.Walls.rc44_sdiff_erase_of_not_mem E R a

/--
[rc44_sdiff_erase_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_sdiff_erase_of_mem_eq
  [Fintype α]
  [DecidableEq α]
  {E R : Finset α}
  {a : α}
-- given
  (haR : a ∈ R) :
-- imply
  (E.erase a) \ (R.erase a) = E \ R := by
-- proof
  apply StatMech.Walls.rc44_sdiff_erase_of_mem E R a haR

/--
[rc44_reflInterE_slab0_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reflInterE_slab0_card_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (haE : a ∈ E) :
-- imply
  ((rc44_reflInterE E 𝒜 ℬ).filter (fun R => a ∉ R)).card = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card := by
-- proof
  apply StatMech.Walls.rc44_reflInterE_slab0_card E a haE 𝒜 ℬ

/--
[rc44_reflInterE_slab1_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reflInterE_slab1_card_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {a : α}
  {𝒜 ℬ : Finset (Finset α)}
-- given
  (haE : a ∈ E) :
-- imply
  ((rc44_reflInterE E 𝒜 ℬ).filter (fun R => a ∈ R)).card = (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card := by
-- proof
  apply StatMech.Walls.rc44_reflInterE_slab1_card E a haE 𝒜 ℬ

/--
[rc44_reflInterE_card_recursion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reflInterE_card_recursion_eq
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
  apply StatMech.Walls.rc44_reflInterE_card_recursion E a haE 𝒜 ℬ

/--
[rc44_famCylBoxEComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_famCylBoxEComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_famCylBoxEComp E 𝒜 ℬ = rc44_famCylBoxE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc44_famCylBoxEComp_eq E 𝒜 ℬ

/--
[rc44_reflInterEComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reflInterEComp_eq_eq
  [Fintype α]
  [DecidableEq α]
  {E : Finset α}
  {𝒜 ℬ : Finset (Finset α)} :
-- imply
  rc44_reflInterEComp E 𝒜 ℬ = rc44_reflInterE E 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc44_reflInterEComp_eq E 𝒜 ℬ

/--
[rc44_diagonalSlab_charge_fails_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_diagonalSlab_charge_fails_fin3_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  ({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1} (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref) ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref) ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref) := by
-- proof
  apply StatMech.Walls.rc44_diagonalSlab_charge_fails_fin3

/--
[rc44_boxMonoResidue_iff_famCylBoxResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_boxMonoResidue_iff_famCylBoxResidue_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue := by
-- proof
  apply StatMech.Walls.rc44_boxMonoResidue_iff_famCylBoxResidue

/--
[rc44_reimer_closes_of_boxMonoResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reimer_closes_of_boxMonoResidue_eq
  [Fintype α]
  [DecidableEq α]
-- given
  (h : rc44_BoxMonoResidue) :
-- imply
  rc18_CylBoxReflInter := by
-- proof
  apply StatMech.Walls.rc44_reimer_closes_of_boxMonoResidue h

/--
[rc44_boxMonoResidue_fin2](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_boxMonoResidue_fin2_eq
  [Fintype α]
  [DecidableEq α]
  {𝒜 ℬ : Finset (Finset (Fin 2))} :
-- imply
  #(rc44_famCylBoxE Finset.univ 𝒜 ℬ) ≤ #(rc44_reflInterE Finset.univ 𝒜 ℬ) := by
-- proof
  apply StatMech.Walls.rc44_boxMonoResidue_fin2 𝒜 ℬ

/--
[rc44_reimer_coordinate_induction](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc44boxineq.lean)
-/
@[path]
private lemma rc44_reimer_coordinate_induction_eq
  [Fintype α]
  [DecidableEq α] :
-- imply
  (rc44_BoxMonoResidue ↔ rc20_FamCylBoxResidue) ∧ (rc44_BoxMonoResidue → rc18_CylBoxReflInter) ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)), rc44_slab0 a (rc44_famCylBoxE E 𝒜 ℬ) ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab0 a ℬ)) ∧ (∀ (E : Finset α) (a : α) (𝒜 ℬ : Finset (Finset α)), rc44_slab1 a (rc44_famCylBoxE E 𝒜 ℬ) ⊆ rc44_famCylBoxE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab1 a ℬ)) ∧ (∀ (E : Finset α) (a : α), a ∈ E → ∀ (𝒜 ℬ : Finset (Finset α)), (rc44_reflInterE E 𝒜 ℬ).card = (rc44_reflInterE (E.erase a) (rc44_slab0 a 𝒜) (rc44_slab1 a ℬ)).card + (rc44_reflInterE (E.erase a) (rc44_slab1 a 𝒜) (rc44_slab0 a ℬ)).card) ∧ (({1} : Finset (Fin 3)) ∈ rc44_famCylBoxEComp {0, 1} (rc44_slab0 2 rc44_Aref) (rc44_slab0 2 rc44_Bref) ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1} (rc44_slab0 2 rc44_Aref) (rc44_slab1 2 rc44_Bref) ∧ ({1} : Finset (Fin 3)) ∉ rc44_reflInterEComp {0, 1} (rc44_slab1 2 rc44_Aref) (rc44_slab0 2 rc44_Bref)) := by
-- proof
  apply StatMech.Walls.rc44_reimer_coordinate_induction


-- created on 2026-10-23
