import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc85smallfamily
open Finset StatMech StatMech.Walls


/--
[rc85_occ_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_occ_empty_eq
  [Fintype ι]
  [DecidableEq ι]
  {K : Finset ι}
  {w : ConfigSpace ι} :
-- imply
  rc80_occ (∅ : Finset (ConfigSpace ι)) K w = false := by
-- proof
  apply StatMech.Walls.rc85_occ_empty K w

/--
[rc85_disjOccG_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_disjOccG_empty_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B = ∅ := by
-- proof
  apply StatMech.Walls.rc85_disjOccG_empty_left B

/--
[rc85_disjOccG_empty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_disjOccG_empty_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG A (∅ : Finset (ConfigSpace ι)) = ∅ := by
-- proof
  apply StatMech.Walls.rc85_disjOccG_empty_right A

/--
[rc85_wall_empty_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_wall_empty_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card := by
-- proof
  apply StatMech.Walls.rc85_wall_empty_left B

/--
[rc85_wall_empty_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_wall_empty_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card := by
-- proof
  apply StatMech.Walls.rc85_wall_empty_right A

/--
[rc85_occ_singleton_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_occ_singleton_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {a : ConfigSpace ι}
  {K : Finset ι}
  {w : ConfigSpace ι} :
-- imply
  rc80_occ ({a} : Finset (ConfigSpace ι)) K w = true ↔ K = Finset.univ ∧ w = a := by
-- proof
  apply StatMech.Walls.rc85_occ_singleton_iff a K w

/--
[rc80_compl_compl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc80_compl_compl_eq
  [Fintype ι]
  [DecidableEq ι]
  {w : ConfigSpace ι} :
-- imply
  rc80_compl (rc80_compl w) = w := by
-- proof
  apply StatMech.Walls.rc80_compl_compl w

/--
[rc85_occ_empty_set_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_occ_empty_set_iff_eq
  [Fintype ι]
  [DecidableEq ι]
  {B : Finset (ConfigSpace ι)}
  {w : ConfigSpace ι} :
-- imply
  rc80_occ B (∅ : Finset ι) w = true ↔ B = Finset.univ := by
-- proof
  apply StatMech.Walls.rc85_occ_empty_set_iff B w

/--
[rc85_disjOccG_singleton_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_disjOccG_singleton_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {a : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B = if B = Finset.univ then {a} else ∅ := by
-- proof
  apply StatMech.Walls.rc85_disjOccG_singleton_left a B

/--
[rc85_wall_singleton_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_wall_singleton_left_eq
  [Fintype ι]
  [DecidableEq ι]
  {a : ConfigSpace ι}
  {B : Finset (ConfigSpace ι)} :
-- imply
  (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card := by
-- proof
  apply StatMech.Walls.rc85_wall_singleton_left a B

/--
[rc85_disjOccG_singleton_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_disjOccG_singleton_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {b : ConfigSpace ι} :
-- imply
  rc80_disjOccG A ({b} : Finset (ConfigSpace ι)) = if A = Finset.univ then {b} else ∅ := by
-- proof
  apply StatMech.Walls.rc85_disjOccG_singleton_right A b

/--
[rc85_wall_singleton_right](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_wall_singleton_right_eq
  [Fintype ι]
  [DecidableEq ι]
  {A : Finset (ConfigSpace ι)}
  {b : ConfigSpace ι} :
-- imply
  (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card := by
-- proof
  apply StatMech.Walls.rc85_wall_singleton_right A b

/--
[rc85_singletonWitness_left_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_singletonWitness_left_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ).card ≤ (rc80_reflInterG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ).card := by
-- proof
  apply StatMech.Walls.rc85_singletonWitness_left_fin3

/--
[rc85_singletonWitness_disjOcc_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_singletonWitness_disjOcc_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_disjOccG ({(fun _ => true)} : Finset (ConfigSpace (Fin 3))) Finset.univ = {(fun _ => true)} := by
-- proof
  apply StatMech.Walls.rc85_singletonWitness_disjOcc_fin3

/--
[rc85_emptyWitness_fin3](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_emptyWitness_fin3_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  rc80_disjOccG (∅ : Finset (ConfigSpace (Fin 3))) Finset.univ = ∅ := by
-- proof
  apply StatMech.Walls.rc85_emptyWitness_fin3

/--
[rc85_consolidation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_consolidation_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsUpper A → rc80_IsLower B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Finset (ConfigSpace ι)), rc80_IsLower A → rc80_IsUpper B → rc80_disjOccG A B = A ∩ B) ∧ (∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (A₁ B₁ : Finset (ConfigSpace ι)) (A₂ B₂ : Finset (ConfigSpace κ)), (rc80_disjOccG A₁ B₁).card ≤ (rc80_reflInterG A₁ B₁).card → (rc80_disjOccG A₂ B₂).card ≤ (rc80_reflInterG A₂ B₂).card → (rc80_disjOccG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card ≤ (rc80_reflInterG (rc80_prodFam A₁ A₂) (rc80_prodFam B₁ B₂)).card) ∧ (∀ A B : Finset (ConfigSpace (Fin 2)), (rc75_disjOccF A B).card ≤ (rc79_reflInterF A B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc85_consolidation

/--
[rc85_proved_subclasses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_proved_subclasses_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ (B : Finset (ConfigSpace ι)), (rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG ∅ B).card) ∧ (∀ (A : Finset (ConfigSpace ι)), (rc80_disjOccG A (∅ : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A ∅).card) ∧ (∀ (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) := by
-- proof
  apply StatMech.Walls.rc85_proved_subclasses

/--
[rc85_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc85smallfamily.lean)
-/
@[path]
private lemma rc85_status_eq
  [Fintype ι]
  [DecidableEq ι] :
-- imply
  (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (B : Finset (ConfigSpace ι)), rc80_disjOccG (∅ : Finset (ConfigSpace ι)) B = ∅) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)), rc80_disjOccG A (∅ : Finset (ConfigSpace ι)) = ∅) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (K : Finset ι) (w : ConfigSpace ι), rc80_occ ({a} : Finset (ConfigSpace ι)) K w = true ↔ K = Finset.univ ∧ w = a) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (a : ConfigSpace ι) (B : Finset (ConfigSpace ι)), (rc80_disjOccG ({a} : Finset (ConfigSpace ι)) B).card ≤ (rc80_reflInterG {a} B).card) ∧ (∀ {ι : Type} [Fintype ι] [DecidableEq ι] (A : Finset (ConfigSpace ι)) (b : ConfigSpace ι), (rc80_disjOccG A ({b} : Finset (ConfigSpace ι))).card ≤ (rc80_reflInterG A {b}).card) ∧ (rc60_BoxUnionBound → ReimerWprobCore) := by
-- proof
  apply StatMech.Walls.rc85_status


-- created on 2026-10-23
