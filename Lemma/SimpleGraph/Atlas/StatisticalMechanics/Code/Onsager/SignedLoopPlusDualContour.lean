import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Onsager.SignedLoopPlusDualContour
open Finset SimpleGraph Set StatMech StatMech.Onsager


/--
[ons_fvCutEdges_eq_crossEdges_minusSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualContour.lean)
-/
@[path]
private lemma ons_fvCutEdges_eq_crossEdges_minusSet_eq
  {d : Nat}
  {B : Finset (Sym2 (Site d))}
  {config : ConfigSpace (Site d)}
-- given
  (hB : ∀ e ∈ B, e ∈ (hypercubicLattice d).edgeSet) :
-- imply
  ons_fvCutEdges B config = crossEdges (minusSet config) B := by
-- proof
  apply StatMech.Onsager.ons_fvCutEdges_eq_crossEdges_minusSet B config hB

/--
[coe_ons_plusDualContour_eq_faceBoundaryGraph_edgeSet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualContour.lean)
-/
@[path]
private lemma coe_ons_plusDualContour_eq_faceBoundaryGraph_edgeSet_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} → Bool) :
-- imply
  (↑(ons_plusDualContour n tau) : Set (Sym2 (Site 2))) = (faceBoundaryGraph (minusSet (glue (plusField 2) tau))).edgeSet := by
-- proof
  apply StatMech.Onsager.coe_ons_plusDualContour_eq_faceBoundaryGraph_edgeSet n tau

/--
[ons_plusDualContour_isEven](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusDualContour.lean)
-/
@[path]
private lemma ons_plusDualContour_isEven_eq
  {n : Nat}
-- given
  (tau : {x // x ∈ box 2 n} → Bool) :
-- imply
  kwg_IsEven (fun edge : Sym2 (Site 2) ↦ edge) (ons_plusDualContour n tau) := by
-- proof
  apply StatMech.Onsager.ons_plusDualContour_isEven n tau


-- created on 2026-10-23
