import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexDegreeTwoDisagreementStrand.Part16
open Finset StatMech StatMech.FrontierD


/--
[mem_sixVertexLocalDisagreementSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma mem_sixVertexLocalDisagreementSides_eq
  {p q : SixVertexLocalIncomingPattern}
  {d : Fin 4} :
-- imply
  d ∈ sixVertexLocalDisagreementSides p q ↔ p d ≠ q d := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexLocalDisagreementSides p q d

/--
[card_sixVertexLocalDisagreementSides](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma card_sixVertexLocalDisagreementSides_eq
  {p q : SixVertexLocalIncomingPattern} :
-- imply
  (sixVertexLocalDisagreementSides p q).card = ∑ d, if p d ≠ q d then 1 else 0 := by
-- proof
  apply StatMech.FrontierD.card_sixVertexLocalDisagreementSides p q

/--
[existsUnique_mem_ne_of_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma existsUnique_mem_ne_of_card_eq_two_eq
  [DecidableEq α]
  {s : Finset α}
  {d : α}
-- given
  (hcard : s.card = 2)
  (hd : d ∈ s) :
-- imply
  ∃! e, e ∈ s ∧ e ≠ d := by
-- proof
  apply StatMech.FrontierD.existsUnique_mem_ne_of_card_eq_two s d hcard hd

/--
[finsetOther_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma finsetOther_mem_eq
  [DecidableEq α]
  {s : Finset α}
  {d : α}
-- given
  (hcard : s.card = 2)
  (hd : d ∈ s) :
-- imply
  finsetOther s d hcard hd ∈ s := by
-- proof
  apply StatMech.FrontierD.finsetOther_mem s d hcard hd

/--
[finsetOther_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma finsetOther_ne_eq
  [DecidableEq α]
  {s : Finset α}
  {d : α}
-- given
  (hcard : s.card = 2)
  (hd : d ∈ s) :
-- imply
  finsetOther s d hcard hd ≠ d := by
-- proof
  apply StatMech.FrontierD.finsetOther_ne s d hcard hd

/--
[finsetOther_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma finsetOther_involutive_eq
  [DecidableEq α]
  {s : Finset α}
  {d : α}
-- given
  (hcard : s.card = 2)
  (hd : d ∈ s) :
-- imply
  finsetOther s (finsetOther s d hcard hd) hcard (finsetOther_mem s d hcard hd) = d := by
-- proof
  apply StatMech.FrontierD.finsetOther_involutive s d hcard hd

/--
[sixVertexTorusDartBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusDartBondMate_involutive_eq
  {T : EvenTorus}
  {d : SixVertexTorusDart T} :
-- imply
  sixVertexTorusDartBondMate T (sixVertexTorusDartBondMate T d) = d := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDartBondMate_involutive T d

/--
[EvenTorus.one_lt_width](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma one_lt_width_eq
  {T : EvenTorus} :
-- imply
  1 < T.width := by
-- proof
  apply StatMech.FrontierD.EvenTorus.one_lt_width T

/--
[EvenTorus.one_lt_height](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma one_lt_height_eq
  {T : EvenTorus} :
-- imply
  1 < T.height := by
-- proof
  apply StatMech.FrontierD.EvenTorus.one_lt_height T

/--
[sixVertexTorusDartBondMate_vertex_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusDartBondMate_vertex_ne_eq
  {T : EvenTorus}
  {d : SixVertexTorusDart T} :
-- imply
  (sixVertexTorusDartBondMate T d).1 ≠ d.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDartBondMate_vertex_ne T d

/--
[sixVertexTorusDartEdge_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusDartEdge_bondMate_eq
  {T : EvenTorus}
  {d : SixVertexTorusDart T} :
-- imply
  sixVertexTorusDartEdge T (sixVertexTorusDartBondMate T d) = sixVertexTorusDartEdge T d := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDartEdge_bondMate T d

/--
[sixVertexDisagreementBondMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDisagreementBondMate_involutive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta} :
-- imply
  sixVertexDisagreementBondMate (sixVertexDisagreementBondMate d) = d := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementBondMate_involutive d

/--
[sixVertexDisagreementDart_side_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDisagreementDart_side_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta} :
-- imply
  d.1.2 ∈ sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega d.1.1) (sixVertexLocalIncomingPattern eta d.1.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementDart_side_mem d

/--
[sixVertexDisagreementDart_local_card_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDisagreementDart_local_card_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega d.1.1) (sixVertexLocalIncomingPattern eta d.1.1)).card = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDisagreementDart_local_card_eq_two hdegree d

/--
[sixVertexDegreeTwoLocalMate_vertex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_vertex_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoLocalMate hdegree d).1.1 = d.1.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_vertex hdegree d

/--
[sixVertexDegreeTwoLocalMate_involutive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_involutive_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoLocalMate hdegree (sixVertexDegreeTwoLocalMate hdegree d) = d := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_involutive hdegree d

/--
[sixVertexDegreeTwoLocalMate_side_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_side_mem_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoLocalMate hdegree d).1.2 ∈ sixVertexLocalDisagreementSides (sixVertexLocalIncomingPattern omega d.1.1) (sixVertexLocalIncomingPattern eta d.1.1) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_side_mem hdegree d

/--
[sixVertexDegreeTwoLocalMate_side_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_side_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠ d.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_side_ne hdegree d

/--
[sixVertexDegreeTwoLocalMate_ne_bondMate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_ne_bondMate_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoLocalMate hdegree d ≠ sixVertexDisagreementBondMate d := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_ne_bondMate hdegree d

/--
[sixVertexLocalIncoming_ne_at_two_disagreements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexLocalIncoming_ne_at_two_disagreements_eq
  {p q : SixVertexLocalIncomingPattern}
  {d e : Fin 4}
-- given
  (hp : p.Ice)
  (hq : q.Ice)
  (hcard : (sixVertexLocalDisagreementSides p q).card = 2)
  (hd : d ∈ sixVertexLocalDisagreementSides p q)
  (he : e ∈ sixVertexLocalDisagreementSides p q)
  (hne : e ≠ d) :
-- imply
  p e ≠ p d := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncoming_ne_at_two_disagreements p q d e hp hq hcard hd he hne

/--
[sixVertexDegreeTwoLocalMate_incoming_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoLocalMate_incoming_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexLocalIncomingPattern omega (sixVertexDegreeTwoLocalMate hdegree d).1.1 (sixVertexDegreeTwoLocalMate hdegree d).1.2 ≠ sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoLocalMate_incoming_ne homega heta hdegree d

/--
[sixVertexLocalIncomingPattern_bondMate_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexLocalIncomingPattern_bondMate_ne_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {d : SixVertexTorusDart T} :
-- imply
  sixVertexLocalIncomingPattern omega (sixVertexTorusDartBondMate T d).1 (sixVertexTorusDartBondMate T d).2 ≠ sixVertexLocalIncomingPattern omega d.1 d.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexLocalIncomingPattern_bondMate_ne omega d

/--
[sixVertexDegreeTwoStrandSuccessor_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandSuccessor_apply_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandSuccessor hdegree d = sixVertexDisagreementBondMate (sixVertexDegreeTwoLocalMate hdegree d) := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandSuccessor_apply hdegree d

/--
[sixVertexDegreeTwoStrandSuccessor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandSuccessor_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexDegreeTwoStrandSuccessor hdegree d ≠ d := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandSuccessor_ne hdegree d

/--
[sixVertexDegreeTwoStrandSuccessor_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandSuccessor_incoming_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexLocalIncomingPattern omega (sixVertexDegreeTwoStrandSuccessor hdegree d).1.1 (sixVertexDegreeTwoStrandSuccessor hdegree d).1.2 = sixVertexLocalIncomingPattern omega d.1.1 d.1.2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandSuccessor_incoming homega heta hdegree d

/--
[sixVertexOrientedDegreeTwoStrandSuccessor_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexOrientedDegreeTwoStrandSuccessor_val_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree d).1 = sixVertexDegreeTwoStrandSuccessor hdegree d.1 := by
-- proof
  apply StatMech.FrontierD.sixVertexOrientedDegreeTwoStrandSuccessor_val homega heta hdegree d

/--
[sixVertexOrientedDegreeTwoStrandSuccessor_ne](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexOrientedDegreeTwoStrandSuccessor_ne_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree d ≠ d := by
-- proof
  apply StatMech.FrontierD.sixVertexOrientedDegreeTwoStrandSuccessor_ne homega heta hdegree d

/--
[sixVertexOrientedDegreeTwoStrandSuccessor_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexOrientedDegreeTwoStrandSuccessor_support_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (sixVertexOrientedDegreeTwoStrandSuccessor homega heta hdegree).support = Finset.univ := by
-- proof
  apply StatMech.FrontierD.sixVertexOrientedDegreeTwoStrandSuccessor_support homega heta hdegree

/--
[sixVertexTorusDartEdge_outgoingDart](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusDartEdge_outgoingDart_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {e : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusDartEdge T (sixVertexTorusEdgeOutgoingDart omega e) = e := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusDartEdge_outgoingDart omega e

/--
[sixVertexTorusEdgeOutgoingDart_incoming](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusEdgeOutgoingDart_incoming_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {e : SixVertexTorusEdge T} :
-- imply
  sixVertexLocalIncomingPattern omega (sixVertexTorusEdgeOutgoingDart omega e).1 (sixVertexTorusEdgeOutgoingDart omega e).2 = false := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeOutgoingDart_incoming omega e

/--
[sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false_eq
  {T : EvenTorus}
  {omega : SixVertexArrows T}
  {d : SixVertexTorusDart T}
-- given
  (hout : sixVertexLocalIncomingPattern omega d.1 d.2 = false) :
-- imply
  sixVertexTorusEdgeOutgoingDart omega (sixVertexTorusDartEdge T d) = d := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeOutgoingDart_edge_of_incoming_false omega d hout

/--
[sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {e : SixVertexTorusEdge T} :
-- imply
  sixVertexTorusEdgeSeamSign omega eta e = 0 ∨ sixVertexTorusEdgeSeamSign omega eta e = 1 ∨ sixVertexTorusEdgeSeamSign omega eta e = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeSeamSign_eq_zero_or_one_or_neg_one omega eta e

/--
[sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {e : SixVertexTorusEdge T}
-- given
  (hagree : ¬ sixVertexTorusEdgeDisagrees omega eta e) :
-- imply
  sixVertexTorusEdgeSeamSign omega eta e = 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexTorusEdgeSeamSign_eq_zero_of_not_disagrees omega eta e hagree

/--
[sum_sixVertexDisagreementEdge_seamSign](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_sixVertexDisagreementEdge_seamSign_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  (∑ e : SixVertexDisagreementEdge omega eta, sixVertexTorusEdgeSeamSign omega eta e.1) = ∑ e : SixVertexTorusEdge T, sixVertexTorusEdgeSeamSign omega eta e := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDisagreementEdge_seamSign omega eta

/--
[sum_sixVertexTorusEdge_seamSign_eq_fullTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_sixVertexTorusEdge_seamSign_eq_fullTransfer_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T} :
-- imply
  (∑ e : SixVertexTorusEdge T, sixVertexTorusEdgeSeamSign omega eta e) = sixVertexTorusMaskSeamTransfer (sixVertexFullDisagreementMask omega eta) omega eta := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexTorusEdge_seamSign_eq_fullTransfer omega eta

/--
[sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {d : SixVertexOrientedDisagreementDart omega eta}
-- given
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (hne : sixVertexDegreeTwoStrandStepSeamSign hdegree d ≠ 0) :
-- imply
  sixVertexDegreeTwoStrandStepSeamSign hdegree d = 1 ∨ sixVertexDegreeTwoStrandStepSeamSign hdegree d = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandStepSeamSign_of_ne_zero hdegree d hne

/--
[sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∑ d : SixVertexOrientedDisagreementDart omega eta, sixVertexDegreeTwoStrandStepSeamSign hdegree d) = ∑ e : SixVertexDisagreementEdge omega eta, sixVertexTorusEdgeSeamSign omega eta e.1 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDegreeTwoStrandStepSeamSign_eq_edges homega heta hdegree

/--
[sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  (∑ d : SixVertexOrientedDisagreementDart omega eta, sixVertexDegreeTwoStrandStepSeamSign hdegree d) = sixVertexTorusMaskSeamTransfer (sixVertexFullDisagreementMask omega eta) omega eta := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDegreeTwoStrandStepSeamSign_eq_fullTransfer homega heta hdegree

/--
[sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  (∑ d : SixVertexOrientedDisagreementDart omega eta, sixVertexDegreeTwoStrandStepSeamSign hdegree d) = 2 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexDegreeTwoStrandStepSeamSign_eq_two homega heta hdegree n homegaSector hetaSector hn

/--
[sum_map_permOrderedCycleFactor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_map_permOrderedCycleFactor_eq
  [Fintype D]
  [DecidableEq D]
  {sigma cycle : Equiv.Perm D}
  {f : D → Int}
-- given
  (hcycle : cycle ∈ sigma.cycleFactorsFinset) :
-- imply
  ((permOrderedCycleFactor sigma cycle hcycle).map f).sum = ∑ d ∈ cycle.support, f d := by
-- proof
  apply StatMech.FrontierD.sum_map_permOrderedCycleFactor sigma cycle hcycle f

/--
[sum_map_list_flatMap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_map_list_flatMap_eq
  {items : List A}
  {pieces : A → List B}
  {f : B → Int} :
-- imply
  ((items.flatMap pieces).map f).sum = (items.map fun a => ((pieces a).map f).sum).sum := by
-- proof
  apply StatMech.FrontierD.sum_map_list_flatMap items pieces f

/--
[sum_map_finset_toList](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_map_finset_toList_eq
  {items : Finset A}
  {f : A → Int} :
-- imply
  (items.toList.map f).sum = ∑ a ∈ items, f a := by
-- proof
  apply StatMech.FrontierD.sum_map_finset_toList items f

/--
[sum_map_permOrderedAllCycles](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_map_permOrderedAllCycles_eq
  [Fintype D]
  [DecidableEq D]
  {sigma : Equiv.Perm D}
  {f : D → Int}
-- given
  (hsupport : sigma.support = Finset.univ) :
-- imply
  ((permOrderedAllCycles sigma).map f).sum = ∑ d, f d := by
-- proof
  apply StatMech.FrontierD.sum_map_permOrderedAllCycles sigma hsupport f

/--
[sum_map_sixVertexDegreeTwoOrderedAllStrands](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_map_sixVertexDegreeTwoOrderedAllStrands_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {f : SixVertexOrientedDisagreementDart omega eta → Int}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ((sixVertexDegreeTwoOrderedAllStrands homega heta hdegree).map f).sum = ∑ d, f d := by
-- proof
  apply StatMech.FrontierD.sum_map_sixVertexDegreeTwoOrderedAllStrands homega heta hdegree f

/--
[ne_zero_of_intKeepNonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma ne_zero_of_intKeepNonzero_eq
  {z : Int}
-- given
  (h : intKeepNonzero z = true) :
-- imply
  z ≠ 0 := by
-- proof
  apply StatMech.FrontierD.ne_zero_of_intKeepNonzero z h

/--
[sum_filter_intKeepNonzero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sum_filter_intKeepNonzero_eq
  {steps : List Int} :
-- imply
  (steps.filter intKeepNonzero).sum = steps.sum := by
-- proof
  apply StatMech.FrontierD.sum_filter_intKeepNonzero steps

/--
[sixVertexDegreeTwoAllStrandsSeamWord_unitSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAllStrandsSeamWord_unitSteps_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ∀ z ∈ sixVertexDegreeTwoAllStrandsSeamWord homega heta hdegree, z = 1 ∨ z = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAllStrandsSeamWord_unitSteps homega heta hdegree

/--
[sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {n : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta)
  (homegaSector : sixVertexUpCount (svTorusVerticalRows T omega (svFinLast T.height_pos)) = n - 1)
  (hetaSector : sixVertexUpCount (svTorusVerticalRows T eta (svFinLast T.height_pos)) = n + 1)
  (hn : 0 < n) :
-- imply
  (sixVertexDegreeTwoAllStrandsSeamWord homega heta hdegree).sum = 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoAllStrandsSeamWord_sum_eq_two homega heta hdegree n homegaSector hetaSector hn

/--
[sixVertexDegreeTwoStrandSeamWord_unitSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexDegreeTwoDisagreementStrand.lean)
-/
@[path]
private lemma sixVertexDegreeTwoStrandSeamWord_unitSteps_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {seed : SixVertexOrientedDisagreementDart omega eta}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule)
  (hdegree : SixVertexLocallyDegreeTwo omega eta) :
-- imply
  ∀ z ∈ sixVertexDegreeTwoStrandSeamWord homega heta hdegree seed, z = 1 ∨ z = -1 := by
-- proof
  apply StatMech.FrontierD.sixVertexDegreeTwoStrandSeamWord_unitSteps homega heta hdegree seed


-- created on 2026-10-23
