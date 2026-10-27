import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneOrderedDeterminedCutObstruction
open Finset StatMech StatMech.Sharpness


/--
[shb_supportLex_not_local_to_acceptedPath](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCutObstruction.lean)
-/
@[path]
private lemma shb_supportLex_not_local_to_acceptedPath_eq :
-- imply
  ∃ A B : Finset shbK4Edge, A ⊆ shbK4G ∧ B ⊆ shbK4G ∧ shbK4Boundary A = {(0 : Fin 4), 3} ∧ shbK4Boundary B = {(0 : Fin 4), 3} ∧ (shbK4Edge.e03 ∈ A ↔ shbK4Edge.e03 ∈ B) ∧ shbK4SelectsDirect03 A ∧ ¬shbK4SelectsDirect03 B := by
-- proof
  apply StatMech.Sharpness.shb_supportLex_not_local_to_acceptedPath

/--
[shb_no_directEdge_local_characterization](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/BackboneOrderedDeterminedCutObstruction.lean)
-/
@[path]
private lemma shb_no_directEdge_local_characterization_eq :
-- imply
  ¬∃ q : Bool -> Bool, ∀ A : Finset shbK4Edge, A ⊆ shbK4G -> shbK4Boundary A = {(0 : Fin 4), 3} -> decide (shbK4SelectsDirect03 A) = q (decide (shbK4Edge.e03 ∈ A)) := by
-- proof
  apply StatMech.Sharpness.shb_no_directEdge_local_characterization


-- created on 2026-10-23
