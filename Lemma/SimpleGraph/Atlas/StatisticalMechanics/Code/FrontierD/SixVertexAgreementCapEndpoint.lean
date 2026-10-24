import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexAgreementCapEndpoint
open StatMech StatMech.FrontierD


/--
[sixVertexFourByTwo_agreement_followed_head](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma sixVertexFourByTwo_agreement_followed_head_eq
  {edge : SixVertexDirectedTorusEdge sixVertexFourByTwoTorus}
-- given
  (hfollows : edge.Follows sixVertexFourByTwoLowArrows)
  (hagrees : edge.IsAgreement sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows) :
-- imply
  edge.head = sixVertexFourByTwoAgreementSuccessor edge.tail := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_agreement_followed_head edge hfollows hagrees

/--
[SixVertexDirectedSimpleArc.agreement_tail_next](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma agreement_tail_next_eq
  {cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus}
  {i : Fin (cap.length - 1)}
-- given
  (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
  (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows) :
-- imply
  (cap.edge ⟨i.val + 1, by omega⟩).tail = sixVertexFourByTwoAgreementSuccessor (cap.edge ⟨i.val, by omega⟩).tail := by
-- proof
  apply StatMech.FrontierD.SixVertexDirectedSimpleArc.agreement_tail_next cap hfollows hagrees i

/--
[sixVertexFourByTwoCanonicalFirstDisagreementArc_start](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma sixVertexFourByTwoCanonicalFirstDisagreementArc_start_eq :
-- imply
  sixVertexFourByTwoCanonicalFirstDisagreementArc.start = sixVertexFourByTwoVertex 0 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCanonicalFirstDisagreementArc_start

/--
[sixVertexFourByTwoCanonicalFirstDisagreementArc_finish](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma sixVertexFourByTwoCanonicalFirstDisagreementArc_finish_eq :
-- imply
  sixVertexFourByTwoCanonicalFirstDisagreementArc.finish = sixVertexFourByTwoVertex 2 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwoCanonicalFirstDisagreementArc_finish

/--
[sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior_eq
  {cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus}
-- given
  (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
  (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows)
  (hstart : cap.start = sixVertexFourByTwoVertex 2 0)
  (hfinish : cap.finish = sixVertexFourByTwoVertex 0 0) :
-- imply
  exists i : Fin cap.length, (cap.edge i).tail = sixVertexFourByTwoVertex 0 1 := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_agreementCap_hits_disagreementArcInterior cap hfollows hagrees hstart hfinish

/--
[sixVertexFourByTwo_no_internallyDisjointAgreementCap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexAgreementCapEndpoint.lean)
-/
@[path]
private lemma sixVertexFourByTwo_no_internallyDisjointAgreementCap_eq
  {cap : SixVertexDirectedSimpleArc sixVertexFourByTwoTorus}
-- given
  (hfollows : cap.Follows sixVertexFourByTwoLowArrows)
  (hagrees : cap.IsAgreement sixVertexFourByTwoLowArrows sixVertexFourByTwoHighArrows)
  (hstart : cap.start = sixVertexFourByTwoCanonicalFirstDisagreementArc.finish)
  (hfinish : cap.finish = sixVertexFourByTwoCanonicalFirstDisagreementArc.start) :
-- imply
  Not (forall i j, (cap.edge i).tail ≠ (sixVertexFourByTwoCanonicalFirstDisagreementArc.edge j).tail) := by
-- proof
  apply StatMech.FrontierD.sixVertexFourByTwo_no_internallyDisjointAgreementCap cap hfollows hagrees hstart hfinish


-- created on 2026-10-23
