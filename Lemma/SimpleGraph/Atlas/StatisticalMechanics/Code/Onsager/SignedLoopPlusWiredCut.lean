import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Onsager.SignedLoopPlusWiredCut.Part5
open Finset SimpleGraph StatMech StatMech.Onsager


/--
[ons_optionAnchoredEquiv_apply_vertexOfSite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma ons_optionAnchoredEquiv_apply_vertexOfSite_eq
  {d n : Nat}
  {x : Site d}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  (ons_optionAnchoredEquiv tau).1 (ons_plusWiredVertexOfSite d n x) = !(glue (plusField d) tau x) := by
-- proof
  apply StatMech.Onsager.ons_optionAnchoredEquiv_apply_vertexOfSite d n tau x

/--
[mem_plusWiredCut_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma mem_plusWiredCut_iff_eq
  {d n : Nat}
  {edge : ons_PlusWiredBond d n}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  edge ∈ multibondCut (ons_plusWiredBondEnds d n) (ons_optionAnchoredEquiv tau).1 ↔ edge.1 ∈ ons_fvCutEdges (bondFinsetTouch d n) (glue (plusField d) tau) := by
-- proof
  apply StatMech.Onsager.mem_plusWiredCut_iff d n tau edge

/--
[ons_plusWiredCutLattice_eq_fvCutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma ons_plusWiredCutLattice_eq_fvCutEdges_eq
  {d n : Nat}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  ons_plusWiredCutLattice d n tau = ons_fvCutEdges (bondFinsetTouch d n) (glue (plusField d) tau) := by
-- proof
  apply StatMech.Onsager.ons_plusWiredCutLattice_eq_fvCutEdges d n tau

/--
[card_plusWiredCut_eq_fvCutEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma card_plusWiredCut_eq_fvCutEdges_eq
  {d n : Nat}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  (multibondCut (ons_plusWiredBondEnds d n) (ons_optionAnchoredEquiv tau).1).card = (ons_fvCutEdges (bondFinsetTouch d n) (glue (plusField d) tau)).card := by
-- proof
  apply StatMech.Onsager.card_plusWiredCut_eq_fvCutEdges d n tau

/--
[ons_plusLowTempContourDenominator_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma ons_plusLowTempContourDenominator_eq_wired_eq
  {d n : Nat}
  {beta : Real} :
-- imply
  ons_plusLowTempContourDenominator d n beta = ons_plusWiredContourDenominator d n beta := by
-- proof
  apply StatMech.Onsager.ons_plusLowTempContourDenominator_eq_wired d n beta

/--
[ons_plusWiredEndpointSign_eq_pathSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma ons_plusWiredEndpointSign_eq_pathSign_eq
  {d n : Nat}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v}
-- given
  (tau : {x // x ∈ box d n} → Bool) :
-- imply
  ons_plusWiredEndpointSign d n (ons_optionAnchoredEquiv tau).1 u v = ons_plusLowTempPathSign (glue (plusField d) tau) path := by
-- proof
  apply StatMech.Onsager.ons_plusWiredEndpointSign_eq_pathSign d n tau path

/--
[ons_plusLowTempPathNumerator_eq_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma ons_plusLowTempPathNumerator_eq_wired_eq
  {d n : Nat}
  {beta : Real}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v} :
-- imply
  ons_plusLowTempPathNumerator d n beta path = ons_plusWiredPathNumerator d n beta u v := by
-- proof
  apply StatMech.Onsager.ons_plusLowTempPathNumerator_eq_wired d n beta path

/--
[integral_plusMeasure_twoPoint_eq_wiredCutRatio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Onsager/SignedLoopPlusWiredCut.lean)
-/
@[path]
private lemma integral_plusMeasure_twoPoint_eq_wiredCutRatio_eq
  {d n : Nat}
  {beta : Real}
  {u v : Site d}
  {path : (hypercubicLattice d).Walk u v} :
-- imply
  (∫ config, spin config u * spin config v ∂(plusMeasure d n beta 0 : MeasureTheory.Measure (ConfigSpace (Site d)))) = ons_plusWiredPathNumerator d n beta u v / ons_plusWiredContourDenominator d n beta := by
-- proof
  apply StatMech.Onsager.integral_plusMeasure_twoPoint_eq_wiredCutRatio d n beta path


-- created on 2026-10-23
