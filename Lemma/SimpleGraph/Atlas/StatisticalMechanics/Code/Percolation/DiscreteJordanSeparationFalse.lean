import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Percolation.DiscreteJordanSeparationFalse
open Set SimpleGraph StatMech StatMech.Percolation


/--
[djsf_not_bdEdge_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFalse.lean)
-/
@[path]
private lemma djsf_not_bdEdge_empty_eq
  {e : Sym2 (Site 2)} :
-- imply
  ¬ bdEdge (∅ : Set (Site 2)) e := by
-- proof
  apply StatMech.Percolation.djsf_not_bdEdge_empty e

/--
[djsf_faceBoundaryGraph_empty_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFalse.lean)
-/
@[path]
private lemma djsf_faceBoundaryGraph_empty_not_adj_eq
  {f g : Site 2} :
-- imply
  ¬ (faceBoundaryGraph (∅ : Set (Site 2))).Adj f g := by
-- proof
  apply StatMech.Percolation.djsf_faceBoundaryGraph_empty_not_adj f g

/--
[djsf_djs_is_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/DiscreteJordanSeparationFalse.lean)
-/
@[path]
private lemma djsf_djs_is_false_eq :
-- imply
  ¬ DiscreteJordanSeparation := by
-- proof
  apply StatMech.Percolation.djsf_djs_is_false


-- created on 2026-10-23
