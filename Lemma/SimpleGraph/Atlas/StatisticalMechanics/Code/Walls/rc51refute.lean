import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.rc51refute.Part3
open Finset StatMech StatMech.Walls


/--
[rc51_neighbourhoodComp_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_neighbourhoodComp_eq_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
  {S : Finset (Fin n)} :
-- imply
  rc51_neighbourhoodComp n 𝒜 ℬ S = rc49_neighbourhood 𝒜 ℬ S := by
-- proof
  apply StatMech.Walls.rc51_neighbourhoodComp_eq n 𝒜 ℬ S

/--
[rc51_hallCondComp_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_hallCondComp_iff_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))} :
-- imply
  rc51_hallCondComp n 𝒜 ℬ = true ↔ rc49_HallCond 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc51_hallCondComp_iff n 𝒜 ℬ

/--
[rc51_not_hallCond_of_comp_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_not_hallCond_of_comp_false_eq
  {n : ℕ}
  {𝒜 ℬ : Finset (Finset (Fin n))}
-- given
  (h : rc51_hallCondComp n 𝒜 ℬ = false) :
-- imply
  ¬ rc49_HallCond 𝒜 ℬ := by
-- proof
  apply StatMech.Walls.rc51_not_hallCond_of_comp_false n 𝒜 ℬ h

/--
[rc51_hallCond_refuter_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_hallCond_refuter_false_eq :
-- imply
  rc51_hallCondComp 3 rc51_Aref rc51_Bref = false := by
-- proof
  apply StatMech.Walls.rc51_hallCond_refuter_false

/--
[rc51_not_hallCond_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_not_hallCond_refuter_eq :
-- imply
  ¬ rc49_HallCond rc51_Aref rc51_Bref := by
-- proof
  apply StatMech.Walls.rc51_not_hallCond_refuter

/--
[rc51_not_injectiveSelection_refuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_not_injectiveSelection_refuter_eq :
-- imply
  ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref := by
-- proof
  apply StatMech.Walls.rc51_not_injectiveSelection_refuter

/--
[rc51_not_hallDoubled](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_not_hallDoubled_eq :
-- imply
  ¬ rc49_HallDoubled := by
-- proof
  apply StatMech.Walls.rc51_not_hallDoubled

/--
[rc51_not_injectiveSelectionAll](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_not_injectiveSelectionAll_eq :
-- imply
  ¬ rc50_InjectiveSelectionAll := by
-- proof
  apply StatMech.Walls.rc51_not_injectiveSelectionAll

/--
[rc51_box_refuter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_box_refuter_eq_eq :
-- imply
  rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
-- proof
  apply StatMech.Walls.rc51_box_refuter_eq

/--
[rc51_reflInter_refuter_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_reflInter_refuter_eq_eq :
-- imply
  rc10_reflInter rc51_Aref rc51_Bref = {(∅ : Finset (Fin 3)), ({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))} := by
-- proof
  apply StatMech.Walls.rc51_reflInter_refuter_eq

/--
[rc51_wall_refuter_holds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_wall_refuter_holds_eq :
-- imply
  (rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card := by
-- proof
  apply StatMech.Walls.rc51_wall_refuter_holds

/--
[rc51_reimer_route_refuted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/rc51refute.lean)
-/
@[path]
private lemma rc51_reimer_route_refuted_eq :
-- imply
  (rc51_hallCondComp 3 rc51_Aref rc51_Bref = false) ∧ ¬ rc49_HallCond rc51_Aref rc51_Bref ∧ ¬ rc50_InjectiveSelection rc51_Aref rc51_Bref ∧ ¬ rc49_HallDoubled ∧ ¬ rc50_InjectiveSelectionAll ∧ (rc20_famCylBox rc51_Aref rc51_Bref = {({0} : Finset (Fin 3)), ({1} : Finset (Fin 3))}) ∧ ((rc20_famCylBoxComp 3 rc51_Aref rc51_Bref).card ≤ (rc20_reflInterComp 3 rc51_Aref rc51_Bref).card) := by
-- proof
  apply StatMech.Walls.rc51_reimer_route_refuted


-- created on 2026-10-23
