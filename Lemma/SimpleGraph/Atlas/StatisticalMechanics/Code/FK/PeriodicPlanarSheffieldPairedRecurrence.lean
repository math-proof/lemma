import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldPairedRecurrence.Part27
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence


/--
[primalBottomScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalBottomScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  p < mu.real (E.rectSideConnectionEvent data.wideLeft data.wideRight 0 data.shortTop (data.primalBottomSource : Set V) (E.rectBottomBoundaryVertices data.wideLeft data.wideRight 0 data.shortTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.primalBottomScore data

/--
[primalTopScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalTopScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  p < mu.real (E.rectSideConnectionEvent data.wideLeft data.wideRight 0 data.shortTop (data.primalTopSource : Set V) (E.rectTopBoundaryVertices data.wideLeft data.wideRight 0 data.shortTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.primalTopScore data

/--
[primalLeftScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalLeftScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  p < mu.real (E.rectSideConnectionEvent 0 data.narrowRight 0 data.tallTop (data.primalLeftSource : Set V) (E.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.primalLeftScore data

/--
[primalRightScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalRightScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  p < mu.real (E.rectSideConnectionEvent 0 data.narrowRight 0 data.tallTop (data.primalRightSource : Set V) (E.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.primalRightScore data

/--
[dualBottomScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualBottomScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  pDual < muDual.real (Edual.rectSideConnectionEvent data.wideLeft data.wideRight 0 data.shortTop (data.dualBottomSource : Set W) (Edual.rectBottomBoundaryVertices data.wideLeft data.wideRight 0 data.shortTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.dualBottomScore data

/--
[dualTopScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualTopScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  pDual < muDual.real (Edual.rectSideConnectionEvent data.wideLeft data.wideRight 0 data.shortTop (data.dualTopSource : Set W) (Edual.rectTopBoundaryVertices data.wideLeft data.wideRight 0 data.shortTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.dualTopScore data

/--
[dualLeftScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualLeftScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  pDual < muDual.real (Edual.rectSideConnectionEvent 0 data.narrowRight 0 data.tallTop (data.dualLeftSource : Set W) (Edual.rectLeftBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.dualLeftScore data

/--
[dualRightScore](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualRightScore_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {data : PairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual} :
-- imply
  pDual < muDual.real (Edual.rectSideConnectionEvent 0 data.narrowRight 0 data.tallTop (data.dualRightSource : Set W) (Edual.rectRightBoundaryVertices 0 data.narrowRight 0 data.tallTop)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedMixedBoundaryScores.dualRightScore data

/--
[ExactExtentPairedMixedBoundaryScores.enlargeWideRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma enlargeWideRight_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsFiniteMeasure mu]
  [IsFiniteMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {newRight : Int}
-- given
  (hRight : raw.wideRightInt <= newRight) :
-- imply
  Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.enlargeWideRight raw newRight hRight

/--
[ExactExtentPairedMixedBoundaryScores.enlargeWide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma enlargeWide_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsFiniteMeasure mu]
  [IsFiniteMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {newLeft newRight : Int}
-- given
  (hLeft : newLeft <= raw.wideLeftInt)
  (hRight : raw.wideRightInt <= newRight) :
-- imply
  Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.enlargeWide raw newLeft newRight hLeft hRight

/--
[ExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalConnector_subset_narrow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY radius : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
-- given
  (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
  (hright : raw.data.base 0 + raw.data.width + E.connectorMarginRequirement radius <= extentX)
  (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
  (htop : raw.data.base 1 + raw.data.height + E.connectorMarginRequirement radius <= extentY) :
-- imply
  forall v : PreferenceGridVertex raw.data.width raw.data.height, P.shift (raw.data.base + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices 0 extentX 0 extentY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow raw hleft hright hbottom htop

/--
[ExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualConnector_subset_narrow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY radius : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
-- given
  (hleft : (Edual.connectorMarginRequirement radius : Int) <= raw.data.baseDual 0)
  (hright : raw.data.baseDual 0 + raw.data.widthDual + Edual.connectorMarginRequirement radius <= extentX)
  (hbottom : (Edual.connectorMarginRequirement radius : Int) <= raw.data.baseDual 1)
  (htop : raw.data.baseDual 1 + raw.data.heightDual + Edual.connectorMarginRequirement radius <= extentY) :
-- imply
  forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual, Pdual.shift (raw.data.baseDual + preferenceGridSite v) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆ Edual.rectVertices 0 extentX 0 extentY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow raw hleft hright hbottom htop

/--
[ExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalConnector_subset_wide_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY radius : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
-- given
  (hleft : (E.connectorMarginRequirement radius : Int) <= raw.data.base 0)
  (hright : raw.data.base 0 + raw.data.width + E.connectorMarginRequirement radius <= extentX)
  (hbottom : (E.connectorMarginRequirement radius : Int) <= raw.data.base 1)
  (htop : raw.data.base 1 + raw.data.height + E.connectorMarginRequirement radius <= extentY) :
-- imply
  forall v : PreferenceGridVertex raw.data.width raw.data.height, P.shift (raw.data.base + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices raw.data.wideLeft raw.data.wideRight 0 raw.data.shortTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide raw hleft hright hbottom htop

/--
[ExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualConnector_subset_wide_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY radius : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
-- given
  (hleft : (Edual.connectorMarginRequirement radius : Int) <= raw.data.baseDual 0)
  (hright : raw.data.baseDual 0 + raw.data.widthDual + Edual.connectorMarginRequirement radius <= extentX)
  (hbottom : (Edual.connectorMarginRequirement radius : Int) <= raw.data.baseDual 1)
  (htop : raw.data.baseDual 1 + raw.data.heightDual + Edual.connectorMarginRequirement radius <= extentY) :
-- imply
  forall v : PreferenceGridVertex raw.data.widthDual raw.data.heightDual, Pdual.shift (raw.data.baseDual + preferenceGridSite v) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆ Edual.rectVertices raw.data.wideLeft raw.data.wideRight 0 raw.data.shortTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide raw hleft hright hbottom htop

/--
[exists_pairedAlignedConnectorSlack](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pairedAlignedConnectorSlack_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {radius : Nat} :
-- imply
  exists k, PairedAlignedConnectorSlack E Edual family familyDual schedule radius k := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedAlignedConnectorSlack E Edual family familyDual schedule radius

/--
[AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalConnector_subset_narrow_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY radius : Nat}
  {data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius k} :
-- imply
  forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height, P.shift (data.raw.data.base + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices 0 extentX 0 extentY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_narrow data slack

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualConnector_subset_narrow_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY radius : Nat}
  {data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius k} :
-- imply
  forall v : PreferenceGridVertex data.raw.data.widthDual data.raw.data.heightDual, Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆ Edual.rectVertices 0 extentX 0 extentY := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_narrow data slack

/--
[AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalConnector_subset_wide_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY radius : Nat}
  {data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius k} :
-- imply
  forall v : PreferenceGridVertex data.raw.data.width data.raw.data.height, P.shift (data.raw.data.base + preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius radius) : Set V) ⊆ E.rectVertices data.raw.data.wideLeft data.raw.data.wideRight 0 data.raw.data.shortTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.primalConnector_subset_wide data slack

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualConnector_subset_wide_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY radius : Nat}
  {data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {slack : PairedAlignedConnectorSlack E Edual family familyDual schedule radius k} :
-- imply
  forall v : PreferenceGridVertex data.raw.data.widthDual data.raw.data.heightDual, Pdual.shift (data.raw.data.baseDual + preferenceGridSite v) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) ⊆ Edual.rectVertices data.raw.data.wideLeft data.raw.data.wideRight 0 data.raw.data.shortTop := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualConnector_subset_wide data slack

/--
[exists_alignedExactExtentPairedMixedBoundaryScores_atExtents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_alignedExactExtentPairedMixedBoundaryScores_atExtents_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX - (family.baseLeft 0 + schedule.horizontal k))
  (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k + extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
  (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY - (family.baseBottom 1 + schedule.vertical k))
  (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k + extentY - (familyDual.baseBottom 1 + schedule.vertical k))
  (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
  (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
  (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
  (htopP : family.radiusTop (schedule.vertical k) <= extentY)
  (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
  (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
  (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
  (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
-- imply
  Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedExactExtentPairedMixedBoundaryScores_atExtents E Edual mu muDual hTI hTIDual family familyDual schedule k extentX extentY hposX hposXDual hposY hposYDual hleftP hrightP hbottomP htopP hleftD hrightD hbottomD htopD

/--
[exists_pairedMixedBoundaryScores_atExtents](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pairedMixedBoundaryScores_atExtents_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hposX : 0 < family.baseRight 0 - schedule.horizontal k + extentX - (family.baseLeft 0 + schedule.horizontal k))
  (hposXDual : 0 < familyDual.baseRight 0 - schedule.horizontal k + extentX - (familyDual.baseLeft 0 + schedule.horizontal k))
  (hposY : 0 < family.baseTop 1 - schedule.vertical k + extentY - (family.baseBottom 1 + schedule.vertical k))
  (hposYDual : 0 < familyDual.baseTop 1 - schedule.vertical k + extentY - (familyDual.baseBottom 1 + schedule.vertical k))
  (hleftP : family.radiusLeft (schedule.horizontal k) <= extentX)
  (hrightP : family.radiusRight (schedule.horizontal k) <= extentX)
  (hbottomP : family.radiusBottom (schedule.vertical k) <= extentY)
  (htopP : family.radiusTop (schedule.vertical k) <= extentY)
  (hleftD : familyDual.radiusLeft (schedule.horizontal k) <= extentX)
  (hrightD : familyDual.radiusRight (schedule.horizontal k) <= extentX)
  (hbottomD : familyDual.radiusBottom (schedule.vertical k) <= extentY)
  (htopD : familyDual.radiusTop (schedule.vertical k) <= extentY) :
-- imply
  Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedMixedBoundaryScores_atExtents E Edual mu muDual hTI hTIDual family familyDual schedule k extentX extentY hposX hposXDual hposY hposYDual hleftP hrightP hbottomP htopP hleftD hrightD hbottomD htopD

/--
[exists_alignedExactExtentPairedMixedBoundaryScores_thresholds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_alignedExactExtentPairedMixedBoundaryScores_thresholds_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists thresholdX thresholdY, forall {extentX extentY}, thresholdX <= extentX -> thresholdY <= extentY -> Nonempty (AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedExactExtentPairedMixedBoundaryScores_thresholds E Edual mu muDual hTI hTIDual family familyDual schedule k

/--
[exists_exactExtentPairedMixedBoundaryScores_thresholds](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_exactExtentPairedMixedBoundaryScores_thresholds_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists thresholdX thresholdY, forall {extentX extentY}, thresholdX <= extentX -> thresholdY <= extentY -> Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_exactExtentPairedMixedBoundaryScores_thresholds E Edual mu muDual hTI hTIDual family familyDual schedule k

/--
[ExactExtentPairedMixedBoundaryScores.extentX_le_wideSpan](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma extentX_le_wideSpan_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY} :
-- imply
  (extentX : Int) <= raw.wideRightInt - raw.wideLeftInt := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.extentX_le_wideSpan raw

/--
[ExactExtentPairedMixedBoundaryScores.dualVerticalMerge_translate_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualVerticalMerge_translate_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {z : Site 2}
  {a b c d : Real}
  {radius : Nat}
-- given
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hbox : Pdual.shift z '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices a b c d) :
-- imply
  muDual.real (Edual.rectanglePairMergeErrorUnion a b c d (raw.data.dualBottomSource.image (Pdual.shift z)) (raw.data.dualTopSource.image (Pdual.shift z))) <= muDual.real (Pdual.pairMergeErrorUnion raw.data.dualBottomSource raw.data.dualTopSource radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualVerticalMerge_translate_measureReal_le raw hTI z a b c d radius hbox

/--
[ExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_translate_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualHorizontalMerge_translate_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {z : Site 2}
  {a b c d : Real}
  {radius : Nat}
-- given
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hbox : Pdual.shift z '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices a b c d) :
-- imply
  muDual.real (Edual.rectanglePairMergeErrorUnion a b c d (raw.data.dualLeftSource.image (Pdual.shift z)) (raw.data.dualRightSource.image (Pdual.shift z))) <= muDual.real (Pdual.pairMergeErrorUnion raw.data.dualLeftSource raw.data.dualRightSource radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_translate_measureReal_le raw hTI z a b c d radius hbox

/--
[ExactExtentPairedMixedBoundaryScores.dualVerticalCrossing_ge_translate_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualVerticalCrossing_ge_translate_inactive_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {z : Site 2}
  {a b : Real}
  {radius : Nat}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (ha : a <= raw.data.wideLeft + (z 0 : Real))
  (hb : raw.data.wideRight + (z 0 : Real) <= b)
  (hbox : Pdual.shift z '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))) :
-- imply
  muDual.real (Edual.rectSideConnectionEvent raw.data.wideLeft raw.data.wideRight 0 extentY (raw.data.dualBottomSource : Set W) (Edual.rectBottomBoundaryVertices raw.data.wideLeft raw.data.wideRight 0 extentY)) * muDual.real (Edual.rectSideConnectionEvent raw.data.wideLeft raw.data.wideRight 0 extentY (raw.data.dualTopSource : Set W) (Edual.rectTopBoundaryVertices raw.data.wideLeft raw.data.wideRight 0 extentY)) - muDual.real (Pdual.pairMergeErrorUnion raw.data.dualBottomSource raw.data.dualTopSource radius) <= muDual.real (Edual.verticalCrossingEvent a b (z 1 : Real) ((extentY : Real) + (z 1 : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualVerticalCrossing_ge_translate_inactive hFKG raw hTI z a b radius ha hb hbox

/--
[ExactExtentPairedMixedBoundaryScores.dualHorizontalCrossing_ge_translate_inactive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualHorizontalCrossing_ge_translate_inactive_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {extentX extentY : Nat}
  {raw : ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY}
  {z : Site 2}
  {c d : Real}
  {radius : Nat}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hc : c <= (z 1 : Real))
  (hd : (extentY : Real) + (z 1 : Real) <= d)
  (hbox : Pdual.shift z '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d) :
-- imply
  muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY (raw.data.dualLeftSource : Set W) (Edual.rectLeftBoundaryVertices 0 extentX 0 extentY)) * muDual.real (Edual.rectSideConnectionEvent 0 extentX 0 extentY (raw.data.dualRightSource : Set W) (Edual.rectRightBoundaryVertices 0 extentX 0 extentY)) - muDual.real (Pdual.pairMergeErrorUnion raw.data.dualLeftSource raw.data.dualRightSource radius) <= muDual.real (Edual.horizontalCrossingEvent (z 0 : Real) ((extentX : Real) + (z 0 : Real)) c d) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExactExtentPairedMixedBoundaryScores.dualHorizontalCrossing_ge_translate_inactive hFKG raw hTI z c d radius hc hd hbox

/--
[dualVerticalCrossing_translate_inactive_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualVerticalCrossing_translate_inactive_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {raw : forall n, ExactExtentPairedMixedBoundaryScores E Edual mu muDual (S n) (Sdual n) (p n) (pDual n) (extentX n) (extentY n)}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (S : Nat -> Finset V)
  (Sdual : Nat -> Finset W)
  (p pDual : Nat -> Real)
  (extentX extentY radius : Nat -> Nat)
  (hpDual : Tendsto pDual atTop (nhds 1))
  (z : Nat -> Site 2)
  (a b : Nat -> Real)
  (ha : forall n, a n <= (raw n).data.wideLeft + (z n 0 : Real))
  (hb : forall n, (raw n).data.wideRight + (z n 0 : Real) <= b n)
  (hbox : forall n, Pdual.shift (z n) '' (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <= Edual.rectVertices (a n) (b n) (z n 1 : Real) ((extentY n : Real) + (z n 1 : Real)))
  (hmerge : Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion (raw n).data.dualBottomSource (raw n).data.dualTopSource (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (a n) (b n) (z n 1 : Real) ((extentY n : Real) + (z n 1 : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualVerticalCrossing_translate_inactive_tendsto_one E Edual muDual hFKG hTI S Sdual p pDual extentX extentY radius raw hpDual z a b ha hb hbox hmerge

/--
[dualHorizontalCrossing_translate_inactive_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualHorizontalCrossing_translate_inactive_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {raw : forall n, ExactExtentPairedMixedBoundaryScores E Edual mu muDual (S n) (Sdual n) (p n) (pDual n) (extentX n) (extentY n)}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (S : Nat -> Finset V)
  (Sdual : Nat -> Finset W)
  (p pDual : Nat -> Real)
  (extentX extentY radius : Nat -> Nat)
  (hpDual : Tendsto pDual atTop (nhds 1))
  (z : Nat -> Site 2)
  (c d : Nat -> Real)
  (hc : forall n, c n <= (z n 1 : Real))
  (hd : forall n, (extentY n : Real) + (z n 1 : Real) <= d n)
  (hbox : forall n, Pdual.shift (z n) '' (Pdual.orbitBox (Pdual.bufferedRadius (radius n)) : Set W) <= Edual.rectVertices (z n 0 : Real) ((extentX n : Real) + (z n 0 : Real)) (c n) (d n))
  (hmerge : Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion (raw n).data.dualLeftSource (raw n).data.dualRightSource (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (z n 0 : Real) ((extentX n : Real) + (z n 0 : Real)) (c n) (d n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.dualHorizontalCrossing_translate_inactive_tendsto_one E Edual muDual hFKG hTI S Sdual p pDual extentX extentY radius raw hpDual z c d hc hd hbox hmerge

/--
[AlignedExactExtentPairedMixedBoundaryScores.wideSpan_formula](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma wideSpan_formula_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k extentX extentY : Nat}
  {data : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY} :
-- imply
  data.raw.wideRightInt - data.raw.wideLeftInt = pairedWideSpanAtExtentX E Edual family familyDual schedule k extentX := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.wideSpan_formula data

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualLeftSource_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualLeftSource_transport_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'} :
-- imply
  new.raw.data.dualLeftSource = old.raw.data.dualLeftSource.image (Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualLeftSource_transport old new

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualRightSource_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualRightSource_transport_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'}
-- given
  (hExtentX : (extentX' : Int) = extentX + 2 * ((schedule.horizontal k' : Int) - schedule.horizontal k)) :
-- imply
  new.raw.data.dualRightSource = old.raw.data.dualRightSource.image (Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualRightSource_transport old new hExtentX

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualBottomSource_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualBottomSource_transport_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'} :
-- imply
  new.raw.data.dualBottomSource = old.raw.data.dualBottomSource.image (Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualBottomSource_transport old new

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualTopSource_transport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualTopSource_transport_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'}
-- given
  (hExtentY : (extentY' : Int) = extentY + 2 * ((schedule.vertical k' : Int) - schedule.vertical k)) :
-- imply
  new.raw.data.dualTopSource = old.raw.data.dualTopSource.image (Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualTopSource_transport old new hExtentY

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualVerticalMerge_transport_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualVerticalMerge_transport_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' radius : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'}
-- given
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hExtentY : (extentY' : Int) = extentY + 2 * ((schedule.vertical k' : Int) - schedule.vertical k))
  (hbox : Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices new.raw.data.wideLeft new.raw.data.wideRight 0 extentY') :
-- imply
  muDual.real (Edual.rectanglePairMergeErrorUnion new.raw.data.wideLeft new.raw.data.wideRight 0 extentY' new.raw.data.dualBottomSource new.raw.data.dualTopSource) <= muDual.real (Pdual.pairMergeErrorUnion old.raw.data.dualBottomSource old.raw.data.dualTopSource radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualVerticalMerge_transport_measureReal_le hTI old new hExtentY hbox

/--
[AlignedExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_transport_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualHorizontalMerge_transport_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k k' extentX extentY extentX' extentY' radius : Nat}
  {old : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k extentX extentY}
  {new : AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k' extentX' extentY'}
-- given
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hExtentX : (extentX' : Int) = extentX + 2 * ((schedule.horizontal k' : Int) - schedule.horizontal k))
  (hbox : Pdual.shift (horizontalShift ((schedule.horizontal k' : Int) - schedule.horizontal k) + verticalShift ((schedule.vertical k' : Int) - schedule.vertical k)) '' (Pdual.orbitBox (Pdual.bufferedRadius radius) : Set W) <= Edual.rectVertices 0 extentX' 0 extentY') :
-- imply
  muDual.real (Edual.rectanglePairMergeErrorUnion 0 extentX' 0 extentY' new.raw.data.dualLeftSource new.raw.data.dualRightSource) <= muDual.real (Pdual.pairMergeErrorUnion old.raw.data.dualLeftSource old.raw.data.dualRightSource radius) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedExactExtentPairedMixedBoundaryScores.dualHorizontalMerge_transport_measureReal_le hTI old new hExtentX hbox

/--
[nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (AlignedNormalRotatedInsetPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k padding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_alignedNormalRotatedInsetPairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k padding

/--
[nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (AlignedNormalTwoRotatedEndpointPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_alignedNormalTwoRotatedEndpointPairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k

/--
[PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma horizontalCrossing_translate_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.horizontalCrossingEvent a b c d) <= mu.real (E.horizontalCrossingEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_translate_measureReal_le E mu hTI z a b c d

/--
[PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma verticalCrossing_translate_measureReal_le_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {z : Site 2}
  {a b c d : Real}
-- given
  (hTI : P.IsTranslationInvariant mu) :
-- imply
  mu.real (E.verticalCrossingEvent a b c d) <= mu.real (E.verticalCrossingEvent (a + (z 0 : Real)) (b + (z 0 : Real)) (c + (z 1 : Real)) (d + (z 1 : Real))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_translate_measureReal_le E mu hTI z a b c d

/--
[PeriodicPlaneEmbedding.horizontalCrossing_translate_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma horizontalCrossing_translate_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (z : Nat -> Site 2)
  (a b c d : Nat -> Real)
  (hlimit : Tendsto (fun n => mu.real (E.horizontalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.horizontalCrossingEvent (a n + (z n 0 : Real)) (b n + (z n 0 : Real)) (c n + (z n 1 : Real)) (d n + (z n 1 : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.horizontalCrossing_translate_tendsto_one E mu hTI z a b c d hlimit

/--
[PeriodicPlaneEmbedding.verticalCrossing_translate_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma verticalCrossing_translate_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (z : Nat -> Site 2)
  (a b c d : Nat -> Real)
  (hlimit : Tendsto (fun n => mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => mu.real (E.verticalCrossingEvent (a n + (z n 0 : Real)) (b n + (z n 0 : Real)) (c n + (z n 1 : Real)) (d n + (z n 1 : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.verticalCrossing_translate_tendsto_one E mu hTI z a b c d hlimit

/--
[PeriodicPlaneEmbedding.crossingMax_independent_translate_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma crossingMax_independent_translate_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (zH zV : Nat -> Site 2)
  (aH bH cH dH aV bV cV dV : Nat -> Real)
  (hlimit : Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (aH n) (bH n) (cH n) (dH n))) (mu.real (E.verticalCrossingEvent (aV n) (bV n) (cV n) (dV n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (aH n + (zH n 0 : Real)) (bH n + (zH n 0 : Real)) (cH n + (zH n 1 : Real)) (dH n + (zH n 1 : Real)))) (mu.real (E.verticalCrossingEvent (aV n + (zV n 0 : Real)) (bV n + (zV n 0 : Real)) (cV n + (zV n 1 : Real)) (dV n + (zV n 1 : Real))))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.crossingMax_independent_translate_tendsto_one E mu hTI zH zV aH bH cH dH aV bV cV dV hlimit

/--
[exists_matched_commonSquareNormalBoundaryBandData_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_matched_commonSquareNormalBoundaryBandData_ge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {margin : Nat}
  {p pDual : Real}
  {primal : E.NormalBoundaryBandSeed mu S margin p}
  {dual : Edual.NormalBoundaryBandSeed muDual Sdual margin pDual}
  {lower : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists M : Nat, lower <= M /\ Nonempty (E.CommonSquareNormalBoundaryBandData mu S margin M p) /\ Nonempty (Edual.CommonSquareNormalBoundaryBandData muDual Sdual margin M pDual) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_matched_commonSquareNormalBoundaryBandData_ge E Edual mu muDual hTI hTIDual primal dual lower

/--
[PeriodicPlaneEmbedding.exists_commonSquareNormalBoundaryBands_outward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_commonSquareNormalBoundaryBands_outward_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : forall n, E.CommonSquareNormalBoundaryBandData mu (P.orbitBox n) (margin n) (M n) (score n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (score : Nat -> Real)
  (margin M : Nat -> Nat)
  (hscore : Tendsto score atTop (nhds 1))
  (_hscore_le : forall n, score n <= 1)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  exists radius : Nat -> Nat, forall (width height : Nat -> Nat) (hwidth : forall n, 0 < width n) (hheight : forall n, 0 < height n), (forall n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (0 : Fin 2) <= M n) -> (forall n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius n)) (1 : Fin 2) <= M n) -> Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n : Real) (-(M n : Real) - pad n) (M n + height n + pad n : Real))) (mu.real (E.horizontalCrossingEvent (-(M n : Real) - pad n) (M n + width n + pad n : Real) (-(M n : Real)) (M n + height n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_commonSquareNormalBoundaryBands_outward E mu hFKG hTI hunique score margin M data hscore _hscore_le pad hpad

/--
[PeriodicPlaneEmbedding.exists_pointwise_commonSquareNormalBoundaryBands_outward](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pointwise_commonSquareNormalBoundaryBands_outward_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : forall k n, E.CommonSquareNormalBoundaryBandData mu (P.orbitBox n) (margin k n) (M k n) (score k n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (score : Nat -> Nat -> Real)
  (margin M : Nat -> Nat -> Nat)
  (hscore : forall k, Tendsto (score k) atTop (nhds 1))
  (hscore_le : forall k n, score k n <= 1)
  (pad : Nat -> Nat -> Int)
  (hpad : forall k n, 0 <= pad k n)
  (width height : Nat -> Nat -> Nat)
  (hwidth : forall k n, 0 < width k n)
  (hheight : forall k n, 0 < height k n) :
-- imply
  exists radius : Nat -> Nat -> Nat, (forall k n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius k n)) (0 : Fin 2) <= M k n) -> (forall k n, E.orbitBoxCoordinateBound (P.bufferedRadius (radius k n)) (1 : Fin 2) <= M k n) -> forall k, Tendsto (fun n => max (mu.real (E.verticalCrossingEvent (-(M k n : Real)) (M k n + width k n : Real) (-(M k n : Real) - pad k n) (M k n + height k n + pad k n : Real))) (mu.real (E.horizontalCrossingEvent (-(M k n : Real) - pad k n) (M k n + width k n + pad k n : Real) (-(M k n : Real)) (M k n + height k n : Real)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_pointwise_commonSquareNormalBoundaryBands_outward E mu hFKG hTI hunique score margin M data hscore hscore_le pad hpad width height hwidth hheight

/--
[nonempty_alignedCrossNestedThreePairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_alignedCrossNestedThreePairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k padding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_alignedCrossNestedThreePairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k padding

/--
[exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding lowerX lowerY : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists data : AlignedCrossNestedThreePairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual family familyDual schedule k padding, lowerX <= data.currentX /\ lowerY <= data.currentY /\ (lowerX : Int) <= data.current.raw.wideRightInt - data.current.raw.wideLeftInt := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedThreePairedMixedBoundaryScores_ge E Edual mu muDual hTI hTIDual family familyDual schedule k padding lowerX lowerY

/--
[nonempty_alignedRotatedCrossNestedThreePairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_alignedRotatedCrossNestedThreePairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (AlignedCrossNestedThreePairedMixedBoundaryScores E.axisSwap Edual.axisSwap mu muDual S Sdual p pDual family.axisSwap familyDual.axisSwap schedule.axisSwap k padding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_alignedRotatedCrossNestedThreePairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k padding

/--
[exists_alignedCrossNestedPairedSequence_with_primalAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedSequence_with_primalAdjacent_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (p pDual : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1) :
-- imply
  exists data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding, Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (E.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedSequence_with_primalAdjacent E Edual mu muDual hFKG hTI hTIDual hunique p pDual family familyDual hp hp_le padding

/--
[exists_alignedCrossNestedPairedSequence_with_primalAdjacent_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_alignedCrossNestedPairedSequence_with_primalAdjacent_ge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (p pDual : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1)
  (lowerX lowerY : Nat -> Nat) :
-- imply
  exists data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding, (forall n, lowerX n <= (data.triple n).currentX) /\ (forall n, lowerY n <= (data.triple n).currentY) /\ (forall n, (lowerX n : Int) <= (data.triple n).current.raw.wideRightInt - (data.triple n).current.raw.wideLeftInt) /\ Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (E.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_alignedCrossNestedPairedSequence_with_primalAdjacent_ge E Edual mu muDual hFKG hTI hTIDual hunique p pDual family familyDual hp hp_le padding lowerX lowerY

/--
[primalAdjacent_transitionCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalAdjacent_transitionCoordinates_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hlimit : Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (E.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (data.transitionA0 n) (data.transitionB0 n) (data.transitionC0 n + padding) (data.transitionD0 n - padding))) (mu.real (E.verticalCrossingEvent (data.transitionA1 n + padding) (data.transitionB1 n - padding) (data.transitionC1 n) (data.transitionD1 n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.primalAdjacent_transitionCoordinates data hlimit

/--
[primalAdjacent_translatedTransitionCoordinates](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalAdjacent_translatedTransitionCoordinates_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (z0 z1 : Nat -> Site 2)
  (hlimit : Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (E.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (data.transitionA0 n + z0 n 0) (data.transitionB0 n + z0 n 0) (data.transitionC0 n + padding + z0 n 1) (data.transitionD0 n - padding + z0 n 1))) (mu.real (E.verticalCrossingEvent (data.transitionA1 n + padding + z1 n 0) (data.transitionB1 n - padding + z1 n 0) (data.transitionC1 n + z1 n 1) (data.transitionD1 n + z1 n 1)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.primalAdjacent_translatedTransitionCoordinates data hTI z0 z1 hlimit

/--
[endpoint_transitionCoordinates_of_mergeLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma endpoint_transitionCoordinates_of_mergeLimits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1)
  (hmergeVertical : Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY (data.triple n).previous.raw.data.primalBottomSource (data.triple n).previous.raw.data.primalTopSource)) atTop (nhds 0))
  (hmergeHorizontal : Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion 0 (data.triple n).nextX 0 (data.triple n).nextY (data.triple n).next.raw.data.primalLeftSource (data.triple n).next.raw.data.primalRightSource)) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.verticalCrossingEvent (data.transitionA0 n + padding) (data.transitionB0 n - padding) (data.transitionC0 n) (data.transitionD0 n))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.horizontalCrossingEvent (data.transitionA1 n) (data.transitionB1 n) (data.transitionC1 n + padding) (data.transitionD1 n - padding))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.endpoint_transitionCoordinates_of_mergeLimits data hFKG hTI hp hp_le hmergeVertical hmergeHorizontal

/--
[dual_endpoint_transitionCoordinates_of_mergeLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dual_endpoint_transitionCoordinates_of_mergeLimits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hp : Tendsto pDual atTop (nhds 1))
  (hp_le : forall n, pDual n <= 1)
  (hmergeVertical : Tendsto (fun n => muDual.real (Edual.rectanglePairMergeErrorUnion (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY (data.triple n).previous.raw.data.dualBottomSource (data.triple n).previous.raw.data.dualTopSource)) atTop (nhds 0))
  (hmergeHorizontal : Tendsto (fun n => muDual.real (Edual.rectanglePairMergeErrorUnion 0 (data.triple n).nextX 0 (data.triple n).nextY (data.triple n).next.raw.data.dualLeftSource (data.triple n).next.raw.data.dualRightSource)) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (data.transitionA0 n + padding) (data.transitionB0 n - padding) (data.transitionC0 n) (data.transitionD0 n))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (data.transitionA1 n) (data.transitionB1 n) (data.transitionC1 n + padding) (data.transitionD1 n - padding))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.dual_endpoint_transitionCoordinates_of_mergeLimits data hFKG hTI hp hp_le hmergeVertical hmergeHorizontal

/--
[exists_endpoint_transitionCoordinates_of_connectorContainment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_endpoint_transitionCoordinates_of_connectorContainment_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1) :
-- imply
  exists verticalRadius horizontalRadius : Nat -> Nat, (forall n, n <= verticalRadius n) /\ (forall n, n <= horizontalRadius n) /\ ((forall n, (P.orbitBox (P.bufferedRadius (verticalRadius n)) : Set V) <= E.rectVertices (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY) -> (forall n, (P.orbitBox (P.bufferedRadius (horizontalRadius n)) : Set V) <= E.rectVertices 0 (data.triple n).nextX 0 (data.triple n).nextY) -> Tendsto (fun n => mu.real (E.verticalCrossingEvent (data.transitionA0 n + padding) (data.transitionB0 n - padding) (data.transitionC0 n) (data.transitionD0 n))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.horizontalCrossingEvent (data.transitionA1 n) (data.transitionB1 n) (data.transitionC1 n + padding) (data.transitionD1 n - padding))) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.exists_endpoint_transitionCoordinates_of_connectorContainment data hFKG hTI hunique hp hp_le

/--
[exists_dual_endpoint_transitionCoordinates_of_connectorContainment](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_dual_endpoint_transitionCoordinates_of_connectorContainment_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
-- given
  (hFKG : IsFKG muDual)
  (hTI : Pdual.IsTranslationInvariant muDual)
  (hunique : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hp : Tendsto pDual atTop (nhds 1))
  (hp_le : forall n, pDual n <= 1) :
-- imply
  exists verticalRadius horizontalRadius : Nat -> Nat, (forall n, n <= verticalRadius n) /\ (forall n, n <= horizontalRadius n) /\ ((forall n, (Pdual.orbitBox (Pdual.bufferedRadius (verticalRadius n)) : Set W) <= Edual.rectVertices (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY) -> (forall n, (Pdual.orbitBox (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <= Edual.rectVertices 0 (data.triple n).nextX 0 (data.triple n).nextY) -> Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (data.transitionA0 n + padding) (data.transitionB0 n - padding) (data.transitionC0 n) (data.transitionD0 n))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (data.transitionA1 n) (data.transitionB1 n) (data.transitionC1 n + padding) (data.transitionD1 n - padding))) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.exists_dual_endpoint_transitionCoordinates_of_connectorContainment data hFKG hTI hunique hp hp_le

/--
[transitionCoordinates_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma transitionCoordinates_spans_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
  {B : Nat}
-- given
  (hpadding : 5 * B < padding) :
-- imply
  (forall n, data.transitionA0 n + 5 * B < data.transitionB0 n - 5 * B) /\ (forall n, data.transitionC0 n + 5 * B < data.transitionD0 n - 5 * B) /\ (forall n, data.transitionA1 n + 5 * B < data.transitionB1 n - 5 * B) /\ (forall n, data.transitionC1 n + 5 * B < data.transitionD1 n - 5 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.transitionCoordinates_spans data B hpadding

/--
[transitionCoordinates_spans_of_current_gt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma transitionCoordinates_spans_of_current_gt_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
  {B : Real}
-- given
  (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
  (hcurrentY : forall n, 10 * B < (data.triple n).currentY) :
-- imply
  (forall n, data.transitionA0 n + 5 * B < data.transitionB0 n - 5 * B) /\ (forall n, data.transitionC0 n + 5 * B < data.transitionD0 n - 5 * B) /\ (forall n, data.transitionA1 n + 5 * B < data.transitionB1 n - 5 * B) /\ (forall n, data.transitionC1 n + 5 * B < data.transitionD1 n - 5 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.transitionCoordinates_spans_of_current_gt data B hcurrentX hcurrentY

/--
[translatedTransitionCoordinates_spans](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma translatedTransitionCoordinates_spans_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {p pDual : Nat -> Real}
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence E Edual mu muDual p pDual family familyDual padding}
  {B : Nat}
-- given
  (hpadding : 5 * B < padding)
  (z0 z1 : Nat -> Site 2) :
-- imply
  (forall n, data.transitionA0 n + z0 n 0 + 5 * B < data.transitionB0 n + z0 n 0 - 5 * B) /\ (forall n, data.transitionC0 n + z0 n 1 + 5 * B < data.transitionD0 n + z0 n 1 - 5 * B) /\ (forall n, data.transitionA1 n + z1 n 0 + 5 * B < data.transitionB1 n + z1 n 0 - 5 * B) /\ (forall n, data.transitionC1 n + z1 n 1 + 5 * B < data.transitionD1 n + z1 n 1 - 5 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.translatedTransitionCoordinates_spans data B hpadding z0 z1

/--
[nonempty_crossNestedThreePairedMixedBoundaryScores](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_crossNestedThreePairedMixedBoundaryScores_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k padding : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  Nonempty (CrossNestedThreePairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual padding) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_crossNestedThreePairedMixedBoundaryScores E Edual mu muDual hTI hTIDual family familyDual schedule k padding

/--
[exists_exactExtentPairedMixedBoundaryScores_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_exactExtentPairedMixedBoundaryScores_ge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {S : Finset V}
  {Sdual : Finset W}
  {p pDual : Real}
  {family : E.NormalBoundaryBandFamily mu S p}
  {familyDual : Edual.NormalBoundaryBandFamily muDual Sdual pDual}
  {verticalRequirement horizontalRequirement : Nat -> Nat}
  {schedule : PairedAlignedMarginSchedule E Edual family familyDual verticalRequirement horizontalRequirement}
  {k minimumX minimumY : Nat}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual) :
-- imply
  exists extentX extentY, minimumX <= extentX /\ minimumY <= extentY /\ Nonempty (ExactExtentPairedMixedBoundaryScores E Edual mu muDual S Sdual p pDual extentX extentY) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_exactExtentPairedMixedBoundaryScores_ge E Edual mu muDual hTI hTIDual family familyDual schedule k minimumX minimumY

/--
[exists_pairedCommonBoundaryPairMergeRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pairedCommonBoundaryPairMergeRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {P : PeriodicGraph V}
  {Pdual : PeriodicGraph W}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {bottom top left right : Finset V}
  {bottomDual topDual leftDual rightDual : Finset W}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  exists radius, cutoff <= radius /\ mu.real (P.pairMergeErrorUnion bottom top radius) < epsilon /\ mu.real (P.pairMergeErrorUnion left right radius) < epsilon /\ muDual.real (Pdual.pairMergeErrorUnion bottomDual topDual radius) < epsilon /\ muDual.real (Pdual.pairMergeErrorUnion leftDual rightDual radius) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedCommonBoundaryPairMergeRadius P Pdual mu muDual hunique huniqueDual bottom top left right bottomDual topDual leftDual rightDual cutoff hepsilon

/--
[nonempty_pairedAlignedMixedLevelStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_pairedAlignedMixedLevelStep_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m)}
  {familyDual : forall m, Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m)}
  {previousScale previousConnector : Nat}
  {scoreEpsilon mergeEpsilon : Real}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (S : Nat -> Finset V)
  (Sdual : Nat -> Finset W)
  (p pDual : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hpDual : Tendsto pDual atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
  (hscoreEpsilon : 0 < scoreEpsilon)
  (hmergeEpsilon : 0 < mergeEpsilon) :
-- imply
  Nonempty (PairedAlignedMixedLevelStep E Edual mu muDual S Sdual p pDual family familyDual verticalRequirement horizontalRequirement previousScale previousConnector scoreEpsilon mergeEpsilon) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_pairedAlignedMixedLevelStep E Edual mu muDual hTI hTIDual hunique huniqueDual S Sdual p pDual family familyDual hp hpDual verticalRequirement horizontalRequirement previousScale previousConnector hscoreEpsilon hmergeEpsilon

/--
[exists_recursivePairedAlignedMixedLevelSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_recursivePairedAlignedMixedLevelSteps_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m)}
  {familyDual : forall m, Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (S : Nat -> Finset V)
  (Sdual : Nat -> Finset W)
  (p pDual : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hpDual : Tendsto pDual atTop (nhds 1))
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
  (scoreEpsilon mergeEpsilon : Nat -> Real)
  (hscoreEpsilon : forall n, 0 < scoreEpsilon n)
  (hmergeEpsilon : forall n, 0 < mergeEpsilon n) :
-- imply
  exists state : Nat -> Nat × Nat, exists steps : forall n, PairedAlignedMixedLevelStep E Edual mu muDual S Sdual p pDual family familyDual verticalRequirement horizontalRequirement (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n), state 0 = (0, 0) /\ forall n, state (n + 1) = ((steps n).scale + 1, (steps n).nextConnector) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_recursivePairedAlignedMixedLevelSteps E Edual mu muDual hTI hTIDual hunique huniqueDual S Sdual p pDual family familyDual hp hpDual verticalRequirement horizontalRequirement scoreEpsilon mergeEpsilon hscoreEpsilon hmergeEpsilon

/--
[exists_recursivePairedAlignedMixedLevelSteps_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_recursivePairedAlignedMixedLevelSteps_with_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall m, E.NormalBoundaryBandFamily mu (S m) (p m)}
  {familyDual : forall m, Edual.NormalBoundaryBandFamily muDual (Sdual m) (pDual m)}
-- given
  (hTI : P.IsTranslationInvariant mu)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (S : Nat -> Finset V)
  (Sdual : Nat -> Finset W)
  (p pDual : Nat -> Real)
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall m, p m <= 1)
  (hpDual : Tendsto pDual atTop (nhds 1))
  (hpDual_le : forall m, pDual m <= 1)
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat) :
-- imply
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real) exists state : Nat -> Nat × Nat, exists steps : forall n, PairedAlignedMixedLevelStep E Edual mu muDual S Sdual p pDual family familyDual verticalRequirement horizontalRequirement (state n).1 (state n).2 (epsilon n) (epsilon n), state 0 = (0, 0) /\ (forall n, state (n + 1) = ((steps n).scale + 1, (steps n).nextConnector)) /\ Tendsto (fun n => (steps n).scale) atTop atTop /\ Tendsto (fun n => p (steps n).scale) atTop (nhds 1) /\ Tendsto (fun n => pDual (steps n).scale) atTop (nhds 1) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).mixed.primalBottomSource (steps n).mixed.primalTopSource (steps n).nextConnector)) atTop (nhds 0) /\ Tendsto (fun n => mu.real (P.pairMergeErrorUnion (steps n).mixed.primalLeftSource (steps n).mixed.primalRightSource (steps n).nextConnector)) atTop (nhds 0) /\ Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion (steps n).mixed.dualBottomSource (steps n).mixed.dualTopSource (steps n).nextConnector)) atTop (nhds 0) /\ Tendsto (fun n => muDual.real (Pdual.pairMergeErrorUnion (steps n).mixed.dualLeftSource (steps n).mixed.dualRightSource (steps n).nextConnector)) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_recursivePairedAlignedMixedLevelSteps_with_limits E Edual mu muDual hTI hTIDual hunique huniqueDual S Sdual p pDual family familyDual hp hp_le hpDual hpDual_le verticalRequirement horizontalRequirement

/--
[exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (f0 f1 f2 f3 f4 : Nat -> Nat -> Real)
  (hf0 : forall k, Tendsto (f0 k) atTop (nhds 1))
  (hf1 : forall k, Tendsto (f1 k) atTop (nhds 1))
  (hf2 : forall k, Tendsto (f2 k) atTop (nhds 1))
  (hf3 : forall k, Tendsto (f3 k) atTop (nhds 1))
  (hf4 : forall k, Tendsto (f4 k) atTop (nhds 1))
  (hle0 : forall k n, f0 k n <= 1)
  (hle1 : forall k n, f1 k n <= 1)
  (hle2 : forall k n, f2 k n <= 1)
  (hle3 : forall k n, f3 k n <= 1)
  (hle4 : forall k n, f4 k n <= 1) :
-- imply
  exists index : Nat -> Nat, (forall n, n <= index n) /\ forall k : Nat -> Nat, (forall n, k n < n + 1) -> Tendsto (fun n => f0 (k n) (index n)) atTop (nhds 1) /\ Tendsto (fun n => f1 (k n) (index n)) atTop (nhds 1) /\ Tendsto (fun n => f2 (k n) (index n)) atTop (nhds 1) /\ Tendsto (fun n => f3 (k n) (index n)) atTop (nhds 1) /\ Tendsto (fun n => f4 (k n) (index n)) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_cofinalIndex_five_uniform_tendsto_one_below_diagonal f0 f1 f2 f3 f4 hf0 hf1 hf2 hf3 hf4 hle0 hle1 hle2 hle3 hle4

/--
[PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.toRecursive](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma toRecursive_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {raw : D.PointwiseRecursiveRectangleArrayCertificate mu} :
-- imply
  Nonempty (D.RecursiveRectangleArrayCertificate mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.toRecursive D mu raw

/--
[PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {raw : D.PointwiseRecursiveRectangleArrayCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PointwiseRecursiveRectangleArrayCertificate.false D mu raw

/--
[PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d : Nat -> Nat -> Real)
  (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
  (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n))) atTop (nhds 1))
  (hhorizontalLevel : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a (k + 1) n) (b (k + 1) n) (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B))) atTop (nhds 1))
  (hnormalAdjacent : forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B) (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
  (hrotatedDualLevel : forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.pointwiseRecursiveRectangleArray_false_of_normal_rotated_limits D mu B hBpos hBp hBd a b c d hspanX hspanY hverticalStart hhorizontalLevel hnormalAdjacent hrotatedDualLevel

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_normal_rotated_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_normal_rotated_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {B : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d : Nat -> Nat -> Real)
  (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
  (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
  (hverticalStart : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a 0 n + 4 * B) (b 0 n - 4 * B) (c 0 n) (d 0 n))) atTop (nhds 1))
  (hhorizontalLevel : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a (k + 1) n) (b (k + 1) n) (c (k + 1) n + 4 * B) (d (k + 1) n - 4 * B))) atTop (nhds 1))
  (hnormalAdjacent : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a (k + 1) n + 4 * B) (b (k + 1) n - 4 * B) (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
  (hrotatedDualLevel : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a k n + 4 * B) (b k n - 4 * B) (c k n) (d k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + 4 * B) (d k n - 4 * B)))) atTop (nhds 1)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_normal_rotated_limits D hp hp1 hq B hBpos hBp hBd a b c d hspanX hspanY hverticalStart hhorizontalLevel hnormalAdjacent hrotatedDualLevel

/--
[PeriodicPlanarDualPair.dualMeasure_crossingMax_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualMeasure_crossingMax_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (aV bV cV dV aH bH cH dH : Nat -> Real)
  (hlimit : Tendsto (fun n => max ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent (aV n) (bV n) (cV n) (dV n))) ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (aV n) (bV n) (cV n) (dV n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (aH n) (bH n) (cH n) (dH n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_crossingMax_tendsto_one D mu aV bV cV dV aH bH cH dH hlimit

/--
[PeriodicPlanarDualPair.dualMeasure_twoLevel_outward_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dualMeasure_twoLevel_outward_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
-- given
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
  (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
  (hdual0 : Tendsto (fun n => max ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))) atTop (nhds 1))
  (hdual1 : Tendsto (fun n => max ((D.dualMeasure mu).real (D.dualEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))) ((D.dualMeasure mu).real (D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))) atTop (nhds 1)) :
-- imply
  Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))) atTop (nhds 1) /\ Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.dualMeasure_twoLevel_outward_limits D mu a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1 hdual0 hdual1

/--
[PeriodicPlanarDualPair.variablePadTwoLevel_false_of_normal_rotated_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadTwoLevel_false_of_normal_rotated_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
  (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
  (hxPad0 : forall n, 4 * B <= xPad0 n)
  (hyPad0 : forall n, 4 * B <= yPad0 n)
  (hxPad1 : forall n, 4 * B <= xPad1 n)
  (hyPad1 : forall n, 4 * B <= yPad1 n)
  (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
  (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
  (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
  (hverticalStart : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) atTop (nhds 1))
  (hhorizontalEnd : Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))) atTop (nhds 1))
  (hnormalAdjacent : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))) atTop (nhds 1))
  (hrotatedDual0 : Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))) atTop (nhds 1))
  (hrotatedDual1 : Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadTwoLevel_false_of_normal_rotated_limits D mu B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1 hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1 hverticalStart hhorizontalEnd hnormalAdjacent hrotatedDual0 hrotatedDual1

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_variablePad_normal_rotated_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_variablePad_normal_rotated_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {B : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
  (xPad0 yPad0 xPad1 yPad1 : Nat -> Real)
  (hxPad0 : forall n, 4 * B <= xPad0 n)
  (hyPad0 : forall n, 4 * B <= yPad0 n)
  (hxPad1 : forall n, 4 * B <= xPad1 n)
  (hyPad1 : forall n, 4 * B <= yPad1 n)
  (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
  (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
  (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
  (hverticalStart : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) atTop (nhds 1))
  (hhorizontalEnd : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n))) atTop (nhds 1))
  (hnormalAdjacent : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n)))) atTop (nhds 1))
  (hrotatedDual0 : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 n + xPad0 n) (b0 n - xPad0 n) (c0 n) (d0 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + yPad0 n) (d0 n - yPad0 n)))) atTop (nhds 1))
  (hrotatedDual1 : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a1 n + xPad1 n) (b1 n - xPad1 n) (c1 n) (d1 n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + yPad1 n) (d1 n - yPad1 n)))) atTop (nhds 1)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_variablePad_normal_rotated_limits D hp hp1 hq B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1 hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1 hverticalStart hhorizontalEnd hnormalAdjacent hrotatedDual0 hrotatedDual1

/--
[PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadTwoLevel_false_of_pointwise_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d xPad yPad : Nat -> Nat -> Real)
  (hxPad : forall k n, 4 * B <= xPad k n)
  (hyPad : forall k n, 4 * B <= yPad k n)
  (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
  (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
  (hvertical : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))) atTop (nhds 1))
  (hhorizontal : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a (k + 1) n) (b (k + 1) n) (c (k + 1) n + yPad (k + 1) n) (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
  (hnormal : forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a (k + 1) n + xPad (k + 1) n) (b (k + 1) n - xPad (k + 1) n) (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
  (hdual : forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_limits D mu B hBpos hBp hBd a b c d xPad yPad hxPad hyPad hspanX hspanY hvertical hhorizontal hnormal hdual

/--
[PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_transitions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadTwoLevel_false_of_pointwise_transitions_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
  (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
  (hxPad0 : forall k n, 4 * B <= xPad0 k n)
  (hyPad0 : forall k n, 4 * B <= yPad0 k n)
  (hxPad1 : forall k n, 4 * B <= xPad1 k n)
  (hyPad1 : forall k n, 4 * B <= yPad1 k n)
  (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
  (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
  (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
  (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
  (hvertical : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))) atTop (nhds 1))
  (hhorizontal : forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a1 k n) (b1 k n) (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))) atTop (nhds 1))
  (hnormal : forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 k n) (b0 k n) (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))) atTop (nhds 1))
  (hdual0 : forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a0 k n) (b0 k n) (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))) atTop (nhds 1))
  (hdual1 : forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 k n) (b1 k n) (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadTwoLevel_false_of_pointwise_transitions D mu B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1 hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1 hvertical hhorizontal hnormal hdual0 hdual1

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_transitions](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_transitions_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {B : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Nat -> Real)
  (xPad0 yPad0 xPad1 yPad1 : Nat -> Nat -> Real)
  (hxPad0 : forall k n, 4 * B <= xPad0 k n)
  (hyPad0 : forall k n, 4 * B <= yPad0 k n)
  (hxPad1 : forall k n, 4 * B <= xPad1 k n)
  (hyPad1 : forall k n, 4 * B <= yPad1 k n)
  (hspanX0 : forall k n, a0 k n + 5 * B < b0 k n - 5 * B)
  (hspanY0 : forall k n, c0 k n + 5 * B < d0 k n - 5 * B)
  (hspanX1 : forall k n, a1 k n + 5 * B < b1 k n - 5 * B)
  (hspanY1 : forall k n, c1 k n + 5 * B < d1 k n - 5 * B)
  (hvertical : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))) atTop (nhds 1))
  (hhorizontal : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a1 k n) (b1 k n) (c1 k n + yPad1 k n) (d1 k n - yPad1 k n))) atTop (nhds 1))
  (hnormal : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 k n) (b0 k n) (c0 k n + yPad0 k n) (d0 k n - yPad0 k n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n)))) atTop (nhds 1))
  (hdual0 : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 k n + xPad0 k n) (b0 k n - xPad0 k n) (c0 k n) (d0 k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a0 k n) (b0 k n) (c0 k n + yPad0 k n) (d0 k n - yPad0 k n)))) atTop (nhds 1))
  (hdual1 : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a1 k n + xPad1 k n) (b1 k n - xPad1 k n) (c1 k n) (d1 k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 k n) (b1 k n) (c1 k n + yPad1 k n) (d1 k n - yPad1 k n)))) atTop (nhds 1)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_transitions D hp hp1 hq B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 xPad0 yPad0 xPad1 yPad1 hxPad0 hyPad0 hxPad1 hyPad1 hspanX0 hspanY0 hspanX1 hspanY1 hvertical hhorizontal hnormal hdual0 hdual1

/--
[PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_variablePad_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_variablePad_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
  {B : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d xPad yPad : Nat -> Nat -> Real)
  (hxPad : forall k n, 4 * B <= xPad k n)
  (hyPad : forall k n, 4 * B <= yPad k n)
  (hspanX : forall k n, a k n + 5 * B < b k n - 5 * B)
  (hspanY : forall k n, c k n + 5 * B < d k n - 5 * B)
  (hvertical : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))) atTop (nhds 1))
  (hhorizontal : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (a (k + 1) n) (b (k + 1) n) (c (k + 1) n + yPad (k + 1) n) (d (k + 1) n - yPad (k + 1) n))) atTop (nhds 1))
  (hnormal : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a (k + 1) n + xPad (k + 1) n) (b (k + 1) n - xPad (k + 1) n) (c (k + 1) n) (d (k + 1) n)))) atTop (nhds 1))
  (hdual : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) forall k, Tendsto (fun n => max (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a k n + xPad k n) (b k n - xPad k n) (c k n) (d k n))) (mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a k n) (b k n) (c k n + yPad k n) (d k n - yPad k n)))) atTop (nhds 1)) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent ≠ 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.freeBufferedInfiniteVolume_commonUnique_measure_ne_one_of_pointwise_variablePad_limits D hp hp1 hq B hBpos hBp hBd a b c d xPad yPad hxPad hyPad hspanX hspanY hvertical hhorizontal hnormal hdual

/--
[PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : D.ComplementaryCrossNestedLimitCertificate mu} :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.ComplementaryCrossNestedLimitCertificate.false D mu data

/--
[PeriodicPlanarDualPair.variablePadComplementaryCrossNested_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadComplementaryCrossNested_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 pad : Nat -> Real)
  (hpad : forall n, 4 * B <= pad n)
  (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
  (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
  (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + pad n) (d0 n - pad n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 n + pad n) (b1 n - pad n) (c1 n) (d1 n)))) atTop (nhds 1))
  (hdualVertical0 : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a0 n + pad n) (b0 n - pad n) (c0 n) (d0 n))) atTop (nhds 1))
  (hdualHorizontal1 : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (c1 n + pad n) (d1 n - pad n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadComplementaryCrossNested_false D mu B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 pad hpad hspanX0 hspanY0 hspanX1 hspanY1 hprimal hdualVertical0 hdualHorizontal1

/--
[PeriodicPlanarDualPair.variablePadComplementaryEndpoints_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadComplementaryEndpoints_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (vLeft vRight vBottom vTop : Nat -> Real)
  (hLeft hRight hBottom hTop pad : Nat -> Real)
  (hpad : forall n, 4 * B <= pad n)
  (hspanVX : forall n, vLeft n - pad n + 5 * B < vRight n + pad n - 5 * B)
  (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
  (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
  (hspanHY : forall n, hBottom n - pad n + 5 * B < hTop n + pad n - 5 * B)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (vLeft n - pad n) (vRight n + pad n) (vBottom n + pad n) (vTop n - pad n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (hLeft n + pad n) (hRight n - pad n) (hBottom n - pad n) (hTop n + pad n)))) atTop (nhds 1))
  (hdualVertical : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1))
  (hdualHorizontal : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadComplementaryEndpoints_false D mu B hBpos hBp hBd vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad hspanVX hspanVY hspanHX hspanHY hprimal hdualVertical hdualHorizontal

/--
[PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_eventSubsets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedCrossing_measureReal_add_le_one_of_eventSubsets_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d : Real}
  {primalEvent : Set (ConfigSpace (Sym2 V))}
  {dualEvent : Set (ConfigSpace (Sym2 W))}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hprimal : primalEvent <= D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B))
  (hdual : dualEvent <= D.dualEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) :
-- imply
  mu.real primalEvent + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_eventSubsets D mu B hBpos hBp hBd a b c d hab hcd primalEvent dualEvent hprimal hdual

/--
[PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d : Real}
  {primalEvent : Set (ConfigSpace (Sym2 V))}
  {dualEvent : Set (ConfigSpace (Sym2 W))}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hprimal : primalEvent <= D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d)
  (hdual : dualEvent <= D.dualEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) :
-- imply
  mu.real primalEvent + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' dualEvent) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_eventSubsets D mu B hBpos hBp hBd a b c d hab hcd primalEvent dualEvent hprimal hdual

/--
[PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d vLeft vRight : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hleft : a + 4 * B <= vLeft)
  (hright : vRight <= b - 4 * B) :
-- imply
  mu.real (D.primalEmbedding.horizontalCrossingEvent a b (c + 4 * B) (d - 4 * B)) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent vLeft vRight c d) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerVerticalStrip D mu B hBpos hBp hBd a b c d vLeft vRight hab hcd hleft hright

/--
[PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a b c d hBottom hTop : Real)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hbottom : c + 4 * B <= hBottom)
  (htop : hTop <= d - 4 * B) :
-- imply
  mu.real (D.primalEmbedding.verticalCrossingEvent (a + 4 * B) (b - 4 * B) c d) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b hBottom hTop) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerHorizontalStrip D mu B hBpos hBp hBd a b c d hBottom hTop hab hcd hbottom htop

/--
[PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerStrips](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedCrossing_measureReal_add_le_one_of_innerStrips_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d primalBottom primalTop dualLeft dualRight : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hprimalBottom : c + 4 * B <= primalBottom)
  (hprimalTop : primalTop <= d - 4 * B)
  (hdualLeft : a + 4 * B <= dualLeft)
  (hdualRight : dualRight <= b - 4 * B) :
-- imply
  mu.real (D.primalEmbedding.horizontalCrossingEvent a b primalBottom primalTop) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent dualLeft dualRight c d) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedCrossing_measureReal_add_le_one_of_innerStrips D mu B hBpos hBp hBd a b c d primalBottom primalTop dualLeft dualRight hab hcd hprimalBottom hprimalTop hdualLeft hdualRight

/--
[PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {a b c d primalLeft primalRight dualBottom dualTop : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hab : a + 5 * B < b - 5 * B)
  (hcd : c + 5 * B < d - 5 * B)
  (hprimalLeft : a + 4 * B <= primalLeft)
  (hprimalRight : primalRight <= b - 4 * B)
  (hdualBottom : c + 4 * B <= dualBottom)
  (hdualTop : dualTop <= d - 4 * B) :
-- imply
  mu.real (D.primalEmbedding.verticalCrossingEvent primalLeft primalRight c d) + mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent a b dualBottom dualTop) <= 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.matchedVerticalHorizontalCrossing_measureReal_add_le_one_of_innerStrips D mu B hBpos hBp hBd a b c d primalLeft primalRight dualBottom dualTop hab hcd hprimalLeft hprimalRight hdualBottom hdualTop

/--
[PeriodicPlanarDualPair.horizontalDualVerticalEndpoint_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma horizontalDualVerticalEndpoint_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
  (hLeft hRight hBottom hTop : Nat -> Real)
  (dualLeft dualRight dualBottom dualTop : Nat -> Real)
  (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
  (hspanDVY : forall n, dualBottom n + 5 * B < dualTop n - 5 * B)
  (hBottomFit : forall n, dualBottom n + 4 * B <= hBottom n)
  (hTopFit : forall n, hTop n <= dualTop n - 4 * B)
  (hLeftFit : forall n, hLeft n + 4 * B <= dualLeft n)
  (hRightFit : forall n, dualRight n <= hRight n - 4 * B)
  (hprimal : Tendsto (fun n => mu.real (D.primalEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1))
  (hdual : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.horizontalDualVerticalEndpoint_false D mu B hBpos hBp hBd hLeft hRight hBottom hTop dualLeft dualRight dualBottom dualTop hspanHX hspanDVY hBottomFit hTopFit hLeftFit hRightFit hprimal hdual

/--
[PeriodicPlanarDualPair.verticalDualHorizontalEndpoint_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma verticalDualHorizontalEndpoint_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
  (vLeft vRight vBottom vTop : Nat -> Real)
  (dualLeft dualRight dualBottom dualTop : Nat -> Real)
  (hspanDHX : forall n, dualLeft n + 5 * B < dualRight n - 5 * B)
  (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
  (hLeftFit : forall n, dualLeft n + 4 * B <= vLeft n)
  (hRightFit : forall n, vRight n <= dualRight n - 4 * B)
  (hBottomFit : forall n, vBottom n + 4 * B <= dualBottom n)
  (hTopFit : forall n, dualTop n <= vTop n - 4 * B)
  (hprimal : Tendsto (fun n => mu.real (D.primalEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1))
  (hdual : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (dualLeft n) (dualRight n) (dualBottom n) (dualTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.verticalDualHorizontalEndpoint_false D mu B hBpos hBp hBd vLeft vRight vBottom vTop dualLeft dualRight dualBottom dualTop hspanDHX hspanVY hLeftFit hRightFit hBottomFit hTopFit hprimal hdual

/--
[PeriodicPlanarDualPair.asymmetricEndpointCoordinates_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma asymmetricEndpointCoordinates_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (a0 b0 c0 d0 a1 b1 c1 d1 : Nat -> Real)
  (vLeft vRight hBottom hTop : Nat -> Real)
  (hspanX0 : forall n, a0 n + 5 * B < b0 n - 5 * B)
  (hspanY0 : forall n, c0 n + 5 * B < d0 n - 5 * B)
  (hspanX1 : forall n, a1 n + 5 * B < b1 n - 5 * B)
  (hspanY1 : forall n, c1 n + 5 * B < d1 n - 5 * B)
  (hvLeft : forall n, a0 n + 4 * B <= vLeft n)
  (hvRight : forall n, vRight n <= b0 n - 4 * B)
  (hhBottom : forall n, c1 n + 4 * B <= hBottom n)
  (hhTop : forall n, hTop n <= d1 n - 4 * B)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (a0 n) (b0 n) (c0 n + 4 * B) (d0 n - 4 * B))) (mu.real (D.primalEmbedding.verticalCrossingEvent (a1 n + 4 * B) (b1 n - 4 * B) (c1 n) (d1 n)))) atTop (nhds 1))
  (hdualV : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (c0 n) (d0 n))) atTop (nhds 1))
  (hdualH : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a1 n) (b1 n) (hBottom n) (hTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.asymmetricEndpointCoordinates_false D mu B hBpos hBp hBd a0 b0 c0 d0 a1 b1 c1 d1 vLeft vRight hBottom hTop hspanX0 hspanY0 hspanX1 hspanY1 hvLeft hvRight hhBottom hhTop hprimal hdualV hdualH

/--
[PeriodicPlanarDualPair.fullyAsymmetricEndpointCoordinates_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma fullyAsymmetricEndpointCoordinates_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hLeft hRight hBottom hTop : Nat -> Real)
  (vLeft vRight vBottom vTop : Nat -> Real)
  (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
  (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
  (hspanHX : forall n, hLeft n + 5 * B < hRight n - 5 * B)
  (hspanDVY : forall n, dualVBottom n + 5 * B < dualVTop n - 5 * B)
  (hspanDHX : forall n, dualHLeft n + 5 * B < dualHRight n - 5 * B)
  (hspanVY : forall n, vBottom n + 5 * B < vTop n - 5 * B)
  (hHBottom : forall n, dualVBottom n + 4 * B <= hBottom n)
  (hHTop : forall n, hTop n <= dualVTop n - 4 * B)
  (hDVLeft : forall n, hLeft n + 4 * B <= dualVLeft n)
  (hDVRight : forall n, dualVRight n <= hRight n - 4 * B)
  (hVLeft : forall n, dualHLeft n + 4 * B <= vLeft n)
  (hVRight : forall n, vRight n <= dualHRight n - 4 * B)
  (hDHBottom : forall n, vBottom n + 4 * B <= dualHBottom n)
  (hDHTop : forall n, dualHTop n <= vTop n - 4 * B)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n))) (mu.real (D.primalEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n)))) atTop (nhds 1))
  (hdualV : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (dualVLeft n) (dualVRight n) (dualVBottom n) (dualVTop n))) atTop (nhds 1))
  (hdualH : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (dualHLeft n) (dualHRight n) (dualHBottom n) (dualHTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.fullyAsymmetricEndpointCoordinates_false D mu B hBpos hBp hBd hLeft hRight hBottom hTop vLeft vRight vBottom vTop dualVLeft dualVRight dualVBottom dualVTop dualHLeft dualHRight dualHBottom dualHTop hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop hprimal hdualV hdualH

/--
[PeriodicPlanarDualPair.finiteStripArmArrays_dualCrossingLimits_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma finiteStripArmArrays_dualCrossingLimits_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
  (hR hC hD : Nat -> Real)
  (hHeight : Nat -> Nat)
  (hLower hUpper : Nat -> Finset V)
  (vR vC vD : Nat -> Real)
  (vWidth : Nat -> Nat)
  (vLower vUpper : Nat -> Finset V)
  (dualVLeft dualVRight dualVBottom dualVTop : Nat -> Real)
  (dualHLeft dualHRight dualHBottom dualHTop : Nat -> Real)
  (hgapH : forall n, 3 * B < hD n - hC n)
  (hgapV : forall n, 3 * B < vD n - vC n)
  (hHorizontalArms : Tendsto (fun n => mu.real (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n))) atTop (nhds 1))
  (hVerticalArms : Tendsto (fun n => mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n))) atTop (nhds 1))
  (hspanHX : forall n, (2 * hC n + hD n) / 3 + 5 * B < (hC n + 2 * hD n) / 3 - 5 * B)
  (hspanDVY : forall n, dualVBottom n + 5 * B < dualVTop n - 5 * B)
  (hspanDHX : forall n, dualHLeft n + 5 * B < dualHRight n - 5 * B)
  (hspanVY : forall n, (2 * vC n + vD n) / 3 + 5 * B < (vC n + 2 * vD n) / 3 - 5 * B)
  (hHBottom : forall n, dualVBottom n + 4 * B <= hR n)
  (hHTop : forall n, hR n + hHeight n <= dualVTop n - 4 * B)
  (hDVLeft : forall n, (2 * hC n + hD n) / 3 + 4 * B <= dualVLeft n)
  (hDVRight : forall n, dualVRight n <= (hC n + 2 * hD n) / 3 - 4 * B)
  (hVLeft : forall n, dualHLeft n + 4 * B <= vR n)
  (hVRight : forall n, vR n + vWidth n <= dualHRight n - 4 * B)
  (hDHBottom : forall n, (2 * vC n + vD n) / 3 + 4 * B <= dualHBottom n)
  (hDHTop : forall n, dualHTop n <= (vC n + 2 * vD n) / 3 - 4 * B)
  (hdualV : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (dualVLeft n) (dualVRight n) (dualVBottom n) (dualVTop n))) atTop (nhds 1))
  (hdualH : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (dualHLeft n) (dualHRight n) (dualHBottom n) (dualHTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteStripArmArrays_dualCrossingLimits_false D mu B hBpos hBp hBd hR hC hD hHeight hLower hUpper vR vC vD vWidth vLower vUpper dualVLeft dualVRight dualVBottom dualVTop dualHLeft dualHRight dualHBottom dualHTop hgapH hgapV hHorizontalArms hVerticalArms hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop hdualV hdualH

/--
[PeriodicPlanarDualPair.finiteStripArmArrays_carriedDual_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma finiteStripArmArrays_carriedDual_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu)}
-- given
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
  (hR hC hD : Nat -> Real)
  (hHeight : Nat -> Nat)
  (hLower hUpper : Nat -> Finset V)
  (vR vC vD : Nat -> Real)
  (vWidth : Nat -> Nat)
  (vLower vUpper : Nat -> Finset V)
  (hgapH : forall n, 3 * B < hD n - hC n)
  (hgapV : forall n, 3 * B < vD n - vC n)
  (hHorizontalArms : Tendsto (fun n => mu.real (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n))) atTop (nhds 1))
  (hVerticalArms : Tendsto (fun n => mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n))) atTop (nhds 1))
  (hspanHX : forall n, (2 * hC n + hD n) / 3 + 5 * B < (hC n + 2 * hD n) / 3 - 5 * B)
  (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
  (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
  (hspanVY : forall n, (2 * vC n + vD n) / 3 + 5 * B < (vC n + 2 * vD n) / 3 - 5 * B)
  (hHBottom : forall n, dual.c n + 4 * B <= hR n)
  (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
  (hDVLeft : forall n, (2 * hC n + hD n) / 3 + 4 * B <= dual.aWide n)
  (hDVRight : forall n, dual.bWide n <= (hC n + 2 * hD n) / 3 - 4 * B)
  (hVLeft : forall n, dual.a n + 4 * B <= vR n)
  (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
  (hDHBottom : forall n, (2 * vC n + vD n) / 3 + 4 * B <= dual.cTall n)
  (hDHTop : forall n, dual.dTall n <= (vC n + 2 * vD n) / 3 - 4 * B) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteStripArmArrays_carriedDual_false D mu hFKGDual B hBpos hBp hBd hR hC hD hHeight hLower hUpper vR vC vD vWidth vLower vUpper hgapH hgapV hHorizontalArms hVerticalArms dual hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop

/--
[PeriodicPlanarDualPair.finiteStripArmArrays_reframedCarriedDual_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma finiteStripArmArrays_reframedCarriedDual_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu)}
-- given
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy u - D.dualEmbedding.vertex x) i| <= B)
  (hR hC hD : Nat -> Real)
  (hHeight : Nat -> Nat)
  (hLower hUpper : Nat -> Finset V)
  (vR vC vD : Nat -> Real)
  (vWidth : Nat -> Nat)
  (vLower vUpper : Nat -> Finset V)
  (hgapH : forall n, 3 * B < hD n - hC n)
  (hgapV : forall n, 3 * B < vD n - vC n)
  (hHorizontalArms : Tendsto (fun n => mu.real (D.primalEmbedding.axisSwap.finiteStripJoinedBoundaryArmEvent (hR n) (hC n) (hD n) (hHeight n) (hLower n) (hUpper n))) atTop (nhds 1))
  (hVerticalArms : Tendsto (fun n => mu.real (D.primalEmbedding.finiteStripJoinedBoundaryArmEvent (vR n) (vC n) (vD n) (vWidth n) (vLower n) (vUpper n))) atTop (nhds 1))
  (hspanHX : forall n, (2 * hC n + hD n) / 3 + 5 * B < (hC n + 2 * hD n) / 3 - 5 * B)
  (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
  (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
  (hspanVY : forall n, (2 * vC n + vD n) / 3 + 5 * B < (vC n + 2 * vD n) / 3 - 5 * B)
  (hHBottom : forall n, dual.c n + 4 * B <= hR n)
  (hHTop : forall n, hR n + hHeight n <= dual.d n - 4 * B)
  (hWideLeft : forall n, (2 * hC n + hD n) / 3 + 4 * B <= min (dual.a n) (-D.dualEmbedding.orbitBoxCoordinateBound (Pdual.bufferedRadius (dual.verticalRadius n)) 0))
  (hWideRight : forall n, max (dual.b n) (D.dualEmbedding.orbitBoxCoordinateBound (Pdual.bufferedRadius (dual.verticalRadius n)) 0) <= (hC n + 2 * hD n) / 3 - 4 * B)
  (hVLeft : forall n, dual.a n + 4 * B <= vR n)
  (hVRight : forall n, vR n + vWidth n <= dual.b n - 4 * B)
  (hTallBottom : forall n, (2 * vC n + vD n) / 3 + 4 * B <= min (dual.c n) (-D.dualEmbedding.orbitBoxCoordinateBound (Pdual.bufferedRadius (dual.horizontalRadius n)) 1))
  (hTallTop : forall n, max (dual.d n) (D.dualEmbedding.orbitBoxCoordinateBound (Pdual.bufferedRadius (dual.horizontalRadius n)) 1) <= (vC n + 2 * vD n) / 3 - 4 * B) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.finiteStripArmArrays_reframedCarriedDual_false D mu hFKGDual B hBpos hBp hBd hR hC hD hHeight hLower hUpper vR vC vD vWidth vLower vUpper hgapH hgapV hHorizontalArms hVerticalArms dual hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hWideLeft hWideRight hVLeft hVRight hTallBottom hTallTop

/--
[PeriodicPlanarDualPair.carriedCrossNestedArrays_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma carriedCrossNestedArrays_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {primal : D.primalEmbedding.CarriedCrossNestedArray mu}
  {dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu)}
-- given
  (hFKG : IsFKG mu)
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hspanHX : forall n, primal.a n + 5 * B < primal.b n - 5 * B)
  (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
  (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
  (hspanVY : forall n, primal.c n + 5 * B < primal.d n - 5 * B)
  (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall n)
  (hHTop : forall n, primal.dTall n <= dual.d n - 4 * B)
  (hDVLeft : forall n, primal.a n + 4 * B <= dual.aWide n)
  (hDVRight : forall n, dual.bWide n <= primal.b n - 4 * B)
  (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide n)
  (hVRight : forall n, primal.bWide n <= dual.b n - 4 * B)
  (hDHBottom : forall n, primal.c n + 4 * B <= dual.cTall n)
  (hDHTop : forall n, dual.dTall n <= primal.d n - 4 * B) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.carriedCrossNestedArrays_false D mu hFKG hFKGDual B hBpos hBp hBd primal dual hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop

/--
[PeriodicPlanarDualPair.carriedCrossNestedArrays_succ_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma carriedCrossNestedArrays_succ_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
  {primal : D.primalEmbedding.CarriedCrossNestedArray mu}
  {dual : D.dualEmbedding.CarriedCrossNestedArray (D.dualMeasure mu)}
-- given
  (hFKG : IsFKG mu)
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hspanHX : forall n, primal.a (n + 1) + 5 * B < primal.b (n + 1) - 5 * B)
  (hspanDVY : forall n, dual.c n + 5 * B < dual.d n - 5 * B)
  (hspanDHX : forall n, dual.a n + 5 * B < dual.b n - 5 * B)
  (hspanVY : forall n, primal.c (n + 1) + 5 * B < primal.d (n + 1) - 5 * B)
  (hHBottom : forall n, dual.c n + 4 * B <= primal.cTall (n + 1))
  (hHTop : forall n, primal.dTall (n + 1) <= dual.d n - 4 * B)
  (hDVLeft : forall n, primal.a (n + 1) + 4 * B <= dual.aWide n)
  (hDVRight : forall n, dual.bWide n <= primal.b (n + 1) - 4 * B)
  (hVLeft : forall n, dual.a n + 4 * B <= primal.aWide (n + 1))
  (hVRight : forall n, primal.bWide (n + 1) <= dual.b n - 4 * B)
  (hDHBottom : forall n, primal.c (n + 1) + 4 * B <= dual.cTall n)
  (hDHTop : forall n, dual.dTall n <= primal.d (n + 1) - 4 * B) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.carriedCrossNestedArrays_succ_false D mu hFKG hFKGDual B hBpos hBp hBd primal dual hspanHX hspanDVY hspanDHX hspanVY hHBottom hHTop hDVLeft hDVRight hVLeft hVRight hDHBottom hDHTop

/--
[asymmetricComplementaryEndpointLimits_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma asymmetricComplementaryEndpointLimits_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (H V dualV dualH : Nat -> Real)
  (hH0 : forall n, 0 <= H n)
  (hV0 : forall n, 0 <= V n)
  (hHdual : forall n, H n + dualV n <= 1)
  (hVdual : forall n, V n + dualH n <= 1)
  (hprimal : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1))
  (hdualV : Tendsto dualV atTop (nhds 1))
  (hdualH : Tendsto dualH atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.asymmetricComplementaryEndpointLimits_false mu H V dualV dualH hH0 hV0 hHdual hVdual hprimal hdualV hdualH

/--
[PeriodicPlanarDualPair.variablePadBranchAlignedComplementary_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma variablePadBranchAlignedComplementary_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (branch : Nat -> Bool)
  (a b c d xPad yPad : Nat -> Real)
  (hxPad : forall n, 4 * B <= xPad n)
  (hyPad : forall n, 4 * B <= yPad n)
  (hspanX : forall n, a n + 5 * B < b n - 5 * B)
  (hspanY : forall n, c n + 5 * B < d n - 5 * B)
  (hprimal : Tendsto (fun n => if branch n then mu.real (D.primalEmbedding.verticalCrossingEvent (a n + xPad n) (b n - xPad n) (c n) (d n)) else mu.real (D.primalEmbedding.horizontalCrossingEvent (a n) (b n) (c n + yPad n) (d n - yPad n))) atTop (nhds 1))
  (hdual : Tendsto (fun n => if branch n then mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (a n) (b n) (c n + yPad n) (d n - yPad n)) else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (a n + xPad n) (b n - xPad n) (c n) (d n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.variablePadBranchAlignedComplementary_false D mu B hBpos hBp hBd branch a b c d xPad yPad hxPad hyPad hspanX hspanY hprimal hdual

/--
[PeriodicPlanarDualPair.outwardBranchAlignedComplementary_false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma outwardBranchAlignedComplementary_false_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (branch : Nat -> Bool)
  (a b c d xPad yPad : Nat -> Real)
  (vLeft vRight vBottom vTop : Nat -> Real)
  (hLeft hRight hBottom hTop : Nat -> Real)
  (hvLeft : forall n, vLeft n = a n + xPad n)
  (hvRight : forall n, vRight n = b n - xPad n)
  (hvBottom : forall n, vBottom n = c n)
  (hvTop : forall n, vTop n = d n)
  (hhLeft : forall n, hLeft n = a n)
  (hhRight : forall n, hRight n = b n)
  (hhBottom : forall n, hBottom n = c n + yPad n)
  (hhTop : forall n, hTop n = d n - yPad n)
  (hxPad : forall n, 4 * B <= xPad n)
  (hyPad : forall n, 4 * B <= yPad n)
  (hspanX : forall n, a n + 5 * B < b n - 5 * B)
  (hspanY : forall n, c n + 5 * B < d n - 5 * B)
  (hprimal : Tendsto (fun n => if branch n then mu.real (D.primalEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n)) else mu.real (D.primalEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1))
  (hdual : Tendsto (fun n => if branch n then mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n)) else mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.outwardBranchAlignedComplementary_false D mu B hBpos hBp hBd branch a b c d xPad yPad vLeft vRight vBottom vTop hLeft hRight hBottom hTop hvLeft hvRight hvBottom hvTop hhLeft hhRight hhBottom hhTop hxPad hyPad hspanX hspanY hprimal hdual

/--
[tendsto_max_one_fixedBranch_subsequence](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma tendsto_max_one_fixedBranch_subsequence_eq
  [DecidableEq V]
  [DecidableEq W]
-- given
  (H V : Nat -> Real)
  (hmax : Tendsto (fun n => max (H n) (V n)) atTop (nhds 1)) :
-- imply
  (exists phi : Nat -> Nat, StrictMono phi /\ (forall n, V (phi n) <= H (phi n)) /\ Tendsto (fun n => H (phi n)) atTop (nhds 1)) \/ (exists phi : Nat -> Nat, StrictMono phi /\ (forall n, H (phi n) <= V (phi n)) /\ Tendsto (fun n => V (phi n)) atTop (nhds 1)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.tendsto_max_one_fixedBranch_subsequence H V hmax

/--
[AlignedCrossNestedPairedSequence.false_of_primalAdjacent_and_dualMergeLimits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_of_primalAdjacent_and_dualMergeLimits_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {p pDual : Nat -> Real}
  {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) p pDual family familyDual padding}
  {B : Real}
-- given
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (hpDual : Tendsto pDual atTop (nhds 1))
  (hpDual_le : forall n, pDual n <= 1)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpadding : 4 * B <= (padding : Real))
  (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
  (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (D.primalEmbedding.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1))
  (hmergeVertical : Tendsto (fun n => (D.dualMeasure mu).real (D.dualEmbedding.rectanglePairMergeErrorUnion (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY (data.triple n).previous.raw.data.dualBottomSource (data.triple n).previous.raw.data.dualTopSource)) atTop (nhds 0))
  (hmergeHorizontal : Tendsto (fun n => (D.dualMeasure mu).real (D.dualEmbedding.rectanglePairMergeErrorUnion 0 (data.triple n).nextX 0 (data.triple n).nextY (data.triple n).next.raw.data.dualLeftSource (data.triple n).next.raw.data.dualRightSource)) atTop (nhds 0)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.false_of_primalAdjacent_and_dualMergeLimits D mu data hFKGDual hTIDual hpDual hpDual_le B hBpos hBp hBd hpadding hcurrentX hcurrentY hprimal hmergeVertical hmergeHorizontal

/--
[AlignedCrossNestedPairedSequence.exists_mixedEndpointRadii_false_of_primalAdjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_mixedEndpointRadii_false_of_primalAdjacent_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {p pDual : Nat -> Real}
  {family : forall n, D.primalEmbedding.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, D.dualEmbedding.NormalBoundaryBandFamily (D.dualMeasure mu) (Pdual.orbitBox n) (pDual n)}
  {padding : Nat}
  {data : AlignedCrossNestedPairedSequence D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) p pDual family familyDual padding}
  {B : Real}
-- given
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (huniqueDual : (D.dualMeasure mu) {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hpDual : Tendsto pDual atTop (nhds 1))
  (hpDual_le : forall n, pDual n <= 1)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpadding : 4 * B <= (padding : Real))
  (hcurrentX : forall n, 10 * B < (data.triple n).currentX)
  (hcurrentY : forall n, 10 * B < (data.triple n).currentY)
  (hprimal : Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (data.triple n).currentX 0 (data.triple n).currentY)) (mu.real (D.primalEmbedding.verticalCrossingEvent (data.triple n).current.raw.data.wideLeft (data.triple n).current.raw.data.wideRight 0 (data.triple n).currentY))) atTop (nhds 1)) :
-- imply
  exists verticalRadius horizontalRadius : Nat -> Nat, (forall n, n <= verticalRadius n) /\ (forall n, n <= horizontalRadius n) /\ ((forall n, (Pdual.orbitBox (Pdual.bufferedRadius (verticalRadius n)) : Set W) <= D.dualEmbedding.rectVertices (data.triple n).previous.raw.data.wideLeft (data.triple n).previous.raw.data.wideRight 0 (data.triple n).previousY) -> (forall n, (Pdual.orbitBox (Pdual.bufferedRadius (horizontalRadius n)) : Set W) <= D.dualEmbedding.rectVertices 0 (data.triple n).nextX 0 (data.triple n).nextY) -> False) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.AlignedCrossNestedPairedSequence.exists_mixedEndpointRadii_false_of_primalAdjacent D mu data hFKGDual hTIDual huniqueDual hpDual hpDual_le B hBpos hBp hBd hpadding hcurrentX hcurrentY hprimal

/--
[PeriodicPlaneEmbedding.exists_deep_adjacentHeight_preference_crossing_branch](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_deep_adjacentHeight_preference_crossing_branch_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {a b c d : Real}
  {t : Int}
  {width height margin : Nat}
  {epsilon : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (ht : 0 <= t)
  (hwidth : 0 < width)
  (hepsilon : 0 <= epsilon)
  (source : PreferenceGridVertex width height -> Finset V)
  (bottom top left right : PreferenceGridVertex width height -> Real)
  (vertical horizontal : PreferenceGridVertex width height -> Bool)
  (hsource : forall x, (source x : Set V) <= E.rectVertices a b c d)
  (hbottomScore : forall x, bottom x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectBottomBoundaryVertices a b c d)))
  (htopScore : forall x, top x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectTopBoundaryVertices a b c d)))
  (hleftScore : forall x, left x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectLeftBoundaryVertices a b c d)))
  (hrightScore : forall x, right x = mu.real (E.rectSideConnectionEvent a b c d (source x : Set V) (E.rectRightBoundaryVertices a b c d)))
  (hverticalBottom : forall v, v.2.val <= margin -> vertical v = true)
  (hverticalTop : forall v, height <= v.2.val + margin -> vertical v = false)
  (hhorizontalLeft : forall v, v.1.val <= margin -> horizontal v = true)
  (hhorizontalRight : forall v, width <= v.1.val + margin -> horizontal v = false)
  (hVtrue : forall v, vertical v = true -> top v <= bottom v + epsilon)
  (hVfalse : forall v, vertical v = false -> bottom v <= top v + epsilon)
  (hHtrue : forall v, horizontal v = true -> right v <= left v + epsilon)
  (hHfalse : forall v, horizontal v = false -> left v <= right v + epsilon) :
-- imply
  exists x xVertical xHorizontal : PreferenceGridVertex width height, KingAdj (preferenceGridSite x) (preferenceGridSite xVertical) /\ KingAdj (preferenceGridSite x) (preferenceGridSite xHorizontal) /\ margin <= x.1.val /\ x.1.val + margin < width /\ margin <= x.2.val /\ x.2.val + margin < height /\ ((1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= bottom x + epsilon /\ let U := (source xVertical).image (P.shift (verticalShift t)) let Mtransfer := mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xVertical)) let Mjoin := mu.real (E.rectanglePairMergeErrorUnion a b c (d + t) (source x) U) bottom x * (mu.real (P.setHitsInfinite (source xVertical : Set V)) * bottom x - Mtransfer - epsilon) - Mjoin <= mu.real (E.verticalCrossingEvent a b c (d + t))) \/ (1 - Real.sqrt (Real.sqrt (1 - mu.real (P.setHitsInfinite (source x : Set V)))) <= left x + epsilon /\ left x * (mu.real (P.setHitsInfinite (source xHorizontal : Set V)) * left x - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) - epsilon) - mu.real (E.rectanglePairMergeErrorUnion a b c d (source x) (source xHorizontal)) <= mu.real (E.horizontalCrossingEvent a b c d))) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_deep_adjacentHeight_preference_crossing_branch E mu hFKG hTI a b c d t ht hwidth epsilon hepsilon source bottom top left right vertical horizontal hsource hbottomScore htopScore hleftScore hrightScore hverticalBottom hverticalTop hhorizontalLeft hhorizontalRight hVtrue hVfalse hHtrue hHfalse

/--
[PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hTI : P.IsTranslationInvariant mu)
  (L R : Nat -> Finset V)
  (radius : Nat -> Nat)
  (z : Nat -> Site 2)
  (a b c d : Nat -> Real)
  (hbox : forall n, (P.shift (z n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a n) (b n) (c n) (d n))
  (hmerge : Tendsto (fun n => mu.real (P.pairMergeErrorUnion (L n) (R n) (radius n))) atTop (nhds 0)) :
-- imply
  Tendsto (fun n => mu.real (E.rectanglePairMergeErrorUnion (a n) (b n) (c n) (d n) ((L n).image (P.shift (z n))) ((R n).image (P.shift (z n))))) atTop (nhds 0) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.translated_rectanglePairMergeErrorUnion_tendsto_zero_of_pairMerge E mu hTI L R radius z a b c d hbox hmerge

/--
[PeriodicPlaneEmbedding.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (radius : Nat -> Nat)
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0)) :
-- imply
  E.UniformTemplateDeepGridAdjacentHeightCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.uniformTemplateDeepGridAdjacentHeightCrossingRadius_of_pairMerge E mu hFKG hTI template htemplateHit step hstep radius hmerge

/--
[PeriodicPlaneEmbedding.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  exists radius : Nat -> Nat, E.UniformTemplateDeepGridAdjacentHeightCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplate_deepGrid_adjacentHeight_crossing_max_tendsto_one E mu hFKG hTI hunique template htemplateHit step hstep

/--
[PeriodicPlaneEmbedding.exists_adjacentHeight_pairMergeRadius_at_error](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_adjacentHeight_pairMergeRadius_at_error_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Finset V}
  {step : Int}
  {cutoff : Nat}
  {epsilon : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hepsilon : 0 < epsilon) :
-- imply
  exists radius : Nat, cutoff <= radius /\ forall q : Fin 2 × (Fin 3 × Fin 3), mu.real (P.pairMergeErrorUnion template (template.image (P.shift (preferenceKingOffset q.2 + if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_adjacentHeight_pairMergeRadius_at_error E mu hunique template step cutoff epsilon hepsilon

/--
[exists_radiusFirst_adjacentEndpointRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_radiusFirst_adjacentEndpointRow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {template : Finset V}
  {step : Int}
  {cutoff : Nat}
  {epsilon : Real}
  {B r y s : Real}
  {t : Int}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (ht : 3 * B < t)
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hhorizontalSpan : forall radius w, minimumWidth radius <= w -> 3 * B < horizontalRight w - horizontalLeft w) :
-- imply
  exists radius width height : Nat, cutoff <= radius /\ minimumWidth radius <= width /\ minimumHeight radius <= height /\ (forall q : Fin 2 × (Fin 3 × Fin 3), mu.real (P.pairMergeErrorUnion template (template.image (P.shift (preferenceKingOffset q.2 + if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon) /\ 1 - epsilon < muDual.real (Edual.verticalCrossingEvent r (r + width) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3)) /\ 1 - epsilon < muDual.real (Edual.horizontalCrossingEvent (horizontalLeft width) (horizontalRight width) y (y + height)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_radiusFirst_adjacentEndpointRow E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon B r y s hB0 hB t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[exists_radiusFirst_dependentGeometry_adjacentEndpointRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_radiusFirst_dependentGeometry_adjacentEndpointRow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {template : Finset V}
  {step : Int}
  {cutoff : Nat}
  {epsilon : Real}
  {B : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (r y s : Nat -> Real)
  (t : Nat -> Int)
  (ht : forall radius, 3 * B < t radius)
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Nat -> Int)
  (hhorizontalSpan : forall radius w, minimumWidth radius <= w -> 3 * B < horizontalRight radius w - horizontalLeft radius w) :
-- imply
  exists radius width height : Nat, cutoff <= radius /\ minimumWidth radius <= width /\ minimumHeight radius <= height /\ (forall q : Fin 2 × (Fin 3 × Fin 3), mu.real (P.pairMergeErrorUnion template (template.image (P.shift (preferenceKingOffset q.2 + if q.1.val = 0 then 0 else verticalShift step))) radius) < epsilon) /\ 1 - epsilon < muDual.real (Edual.verticalCrossingEvent (r radius) (r radius + width) ((2 * s radius + (s radius + t radius)) / 3) ((s radius + 2 * (s radius + t radius)) / 3)) /\ 1 - epsilon < muDual.real (Edual.horizontalCrossingEvent (horizontalLeft radius width) (horizontalRight radius width) (y radius) (y radius + height)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_radiusFirst_dependentGeometry_adjacentEndpointRow E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon B hB0 hB r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[nonempty_radiusFirstAdjacentEndpointRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_radiusFirstAdjacentEndpointRow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {template : Finset V}
  {step : Int}
  {cutoff : Nat}
  {epsilon : Real}
  {B r y s : Real}
  {t : Int}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (ht : 3 * B < t)
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Int)
  (hhorizontalSpan : forall radius w, minimumWidth radius <= w -> 3 * B < horizontalRight w - horizontalLeft w) :
-- imply
  Nonempty (RadiusFirstAdjacentEndpointRow E Edual mu muDual template step cutoff epsilon B r y s t minimumWidth minimumHeight horizontalLeft horizontalRight) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_radiusFirstAdjacentEndpointRow E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon B r y s hB0 hB t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[exists_recursiveRadiusFirstAdjacentEndpointRows_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_recursiveRadiusFirstAdjacentEndpointRows_with_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {B : Real}
  {initialStep : Int}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (hinitialStep : 0 <= initialStep)
  (r y s : Nat -> Int -> Real)
  (t : Nat -> Int -> Int)
  (ht : forall n step, 3 * B < t n step)
  (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Int)
  (hhorizontalSpan : forall n step radius width, minimumWidth n step radius <= width -> 3 * B < horizontalRight n step width - horizontalLeft n step width) :
-- imply
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real) exists state : Nat -> Int × Nat, exists rows : forall n, RadiusFirstAdjacentEndpointRow E Edual mu muDual (template n) (state n).1 (state n).2 (epsilon n) B (r n (state n).1) (y n (state n).1) (s n (state n).1) (t n (state n).1) (minimumWidth n (state n).1) (minimumHeight n (state n).1) (horizontalLeft n (state n).1) (horizontalRight n (state n).1), state 0 = (initialStep, 0) /\ (forall n, state (n + 1) = (((rows n).height : Int), (rows n).radius + 1)) /\ (forall n, 0 <= (state n).1) /\ Tendsto (fun n => (rows n).radius) atTop atTop /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (state n).1))) (rows n).radius)) atTop (nhds 0)) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (state (n + 1)).1))) (rows (n + 1)).radius)) atTop (nhds 0)) /\ Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (r n (state n).1) (r n (state n).1 + (rows n).width) ((2 * s n (state n).1 + (s n (state n).1 + t n (state n).1)) / 3) ((s n (state n).1 + 2 * (s n (state n).1 + t n (state n).1)) / 3))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (horizontalLeft n (state n).1 (rows n).width) (horizontalRight n (state n).1 (rows n).width) (y n (state n).1) (y n (state n).1 + (rows n).height))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_recursiveRadiusFirstAdjacentEndpointRows_with_limits E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hB0 hB template initialStep hinitialStep r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[ExpandedEndpointPrimalBoundaryBandLevel.primalAdjacent_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalAdjacent_limit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {template : Nat -> Finset V}
  {radius : Nat -> Nat}
  {vLeft vRight vBottom vTop pad : Nat -> Real}
  {step : Nat -> Int}
  {level : ExpandedEndpointPrimalBoundaryBandLevel E mu template radius vLeft vRight vBottom vTop pad}
-- given
  (hcontinuation : E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (vLeft n - pad n) (vRight n + pad n) (vBottom n + pad n) (vTop n - pad n))) (mu.real (E.verticalCrossingEvent (vLeft n - pad n) (vRight n + pad n) (vBottom n + pad n) (vTop n - pad n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExpandedEndpointPrimalBoundaryBandLevel.primalAdjacent_limit level hcontinuation

/--
[expandedEndpoint_spans_of_inner_gaps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma expandedEndpoint_spans_of_inner_gaps_eq
  [DecidableEq V]
  [DecidableEq W]
  {B : Real}
-- given
  (hBpos : 0 < B)
  (vLeft vRight vBottom vTop : Nat -> Real)
  (hLeft hRight hBottom hTop pad : Nat -> Real)
  (hpad : forall n, 4 * B <= pad n)
  (hvWidth : forall n, 10 * B < vRight n - vLeft n)
  (hvHeight : forall n, 10 * B < vTop n - vBottom n)
  (hhWidth : forall n, 10 * B < hRight n - hLeft n)
  (hhHeight : forall n, 10 * B < hTop n - hBottom n) :
-- imply
  (forall n, vLeft n - pad n + 5 * B < vRight n + pad n - 5 * B) /\ (forall n, vBottom n + 5 * B < vTop n - 5 * B) /\ (forall n, hLeft n + 5 * B < hRight n - 5 * B) /\ (forall n, hBottom n - pad n + 5 * B < hTop n + pad n - 5 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.expandedEndpoint_spans_of_inner_gaps B hBpos vLeft vRight vBottom vTop hLeft hRight hBottom hTop pad hpad hvWidth hvHeight hhWidth hhHeight

/--
[ExpandedEndpointPrimalBoundaryBandLevel.false_of_alignedEndpoints](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_of_alignedEndpoints_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {template : Nat -> Finset V}
  {radius : Nat -> Nat}
  {vLeft vRight vBottom vTop pad : Nat -> Real}
  {hLeft hRight hBottom hTop : Nat -> Real}
  {step : Nat -> Int}
  {level : ExpandedEndpointPrimalBoundaryBandLevel D.primalEmbedding mu template radius vLeft vRight vBottom vTop pad}
  {B : Real}
-- given
  (hcontinuation : D.primalEmbedding.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius)
  (halignLeft : forall n, hLeft n + pad n = vLeft n - pad n)
  (halignRight : forall n, hRight n - pad n = vRight n + pad n)
  (halignBottom : forall n, hBottom n - pad n = vBottom n + pad n)
  (halignTop : forall n, hTop n + pad n = vTop n - pad n + step n)
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpad : forall n, 4 * B <= pad n)
  (hvWidth : forall n, 10 * B < vRight n - vLeft n)
  (hvHeight : forall n, 10 * B < vTop n - vBottom n)
  (hhWidth : forall n, 10 * B < hRight n - hLeft n)
  (hhHeight : forall n, 10 * B < hTop n - hBottom n)
  (hdualVertical : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.verticalCrossingEvent (vLeft n) (vRight n) (vBottom n) (vTop n))) atTop (nhds 1))
  (hdualHorizontal : Tendsto (fun n => mu.real ((dualConfigEquiv D.edgeDual) ⁻¹' D.dualEmbedding.horizontalCrossingEvent (hLeft n) (hRight n) (hBottom n) (hTop n))) atTop (nhds 1)) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.ExpandedEndpointPrimalBoundaryBandLevel.false_of_alignedEndpoints D mu level hcontinuation halignLeft halignRight halignBottom halignTop B hBpos hBp hBd hpad hvWidth hvHeight hhWidth hhHeight hdualVertical hdualHorizontal

/--
[PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (template : Nat -> Finset V)
  (step : Nat -> Int)
  (radius : Nat -> Nat)
  (hcross : E.UniformTemplateDeepGridAdjacentHeightCrossingRadius mu template step radius) :
-- imply
  E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_deepGrid E mu template step radius hcross

/--
[PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (radius : Nat -> Nat)
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0)) :
-- imply
  E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.uniformTemplateAdjacentBoundaryBandCrossingRadius_of_pairMerge E mu hFKG hTI template htemplateHit step hstep radius hmerge

/--
[PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  exists radius, E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius E mu hFKG hTI hunique template htemplateHit step hstep

/--
[PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (template : Nat -> Finset V)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (template n : Set V))) atTop (nhds 1))
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  exists radius : Nat -> Nat, (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0)) /\ E.UniformTemplateAdjacentBoundaryBandCrossingRadius mu template step radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformTemplateAdjacentBoundaryBandCrossingRadius_with_pairMerge E mu hFKG hTI hunique template htemplateHit step hstep

/--
[PeriodicPlaneEmbedding.exists_uniformAdjacentBoundaryBandRadius_with_cofinalConnectorSchedule](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformAdjacentBoundaryBandRadius_with_cofinalConnectorSchedule_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  exists (radius : Nat -> Nat) (p : Nat -> Real) (family : forall m, E.NormalBoundaryBandFamily mu (P.orbitBox m) (p m)), E.UniformAdjacentBoundaryBandCrossingRadius mu step radius /\ Tendsto p atTop (nhds 1) /\ forall m, (family m).AlignedMarginSchedule E (fun _ => E.connectorMarginRequirement (radius m)) (fun _ => E.connectorMarginRequirement (radius m)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformAdjacentBoundaryBandRadius_with_cofinalConnectorSchedule E mu hFKG hTI hunique step hstep

/--
[PeriodicPlaneEmbedding.exists_uniformOutwardBoundaryCrossingRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformOutwardBoundaryCrossingRadius_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  exists radius, E.UniformOutwardBoundaryCrossingRadius mu pad radius := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformOutwardBoundaryCrossingRadius E mu hFKG hTI hunique pad hpad

/--
[exists_pairedAdjacentBoundaryBandScheduleData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pairedAdjacentBoundaryBandScheduleData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  Nonempty (PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedAdjacentBoundaryBandScheduleData E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual step hstep

/--
[PeriodicPlanarDualPair.exists_canonicalPairedAdjacentBoundaryBandScheduleData_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_canonicalPairedAdjacentBoundaryBandScheduleData_of_common_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Nonempty (PairedAdjacentBoundaryBandScheduleData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_canonicalPairedAdjacentBoundaryBandScheduleData_of_common D hp hp1 hq hcommon step hstep

/--
[exists_pairedAdjacentOutwardScheduleData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_pairedAdjacentOutwardScheduleData_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  Nonempty (PairedAdjacentOutwardScheduleData E Edual mu muDual step pad) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_pairedAdjacentOutwardScheduleData E Edual mu muDual hFKG hTI hunique hFKGDual hTIDual huniqueDual step hstep pad hpad

/--
[PeriodicPlanarDualPair.exists_canonicalPairedAdjacentOutwardScheduleData_of_common](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_canonicalPairedAdjacentOutwardScheduleData_of_common_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {p q : Real}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q)
  (hcommon : let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) mu D.commonUniqueInfiniteClusterEvent = 1)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (pad : Nat -> Int)
  (hpad : forall n, 0 <= pad n) :
-- imply
  let mu : Measure (ConfigSpace (Sym2 V)) := P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) Nonempty (PairedAdjacentOutwardScheduleData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step pad) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_canonicalPairedAdjacentOutwardScheduleData_of_common D hp hp1 hq hcommon step hstep pad hpad

/--
[DualOutwardBoundaryBandLevel.crossing_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma crossing_limit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {step pad : Nat -> Int}
  {data : PairedAdjacentOutwardScheduleData E Edual mu muDual step pad}
  {level : DualOutwardBoundaryBandLevel data} :
-- imply
  Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (level.a n) (level.b n) (level.c n - pad n) (level.d n + pad n))) (muDual.real (Edual.horizontalCrossingEvent (level.a n - pad n) (level.b n + pad n) (level.c n) (level.d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.DualOutwardBoundaryBandLevel.crossing_limit data level

/--
[PairedBoundaryBandLevel.primalAdjacent_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalAdjacent_limit_eq_2
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {step : Nat -> Int}
  {data : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {level : PairedBoundaryBandLevel data} :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (level.a n) (level.b n) (level.c n) (level.d n))) (mu.real (E.verticalCrossingEvent (level.a n) (level.b n) (level.c n) (level.d n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedBoundaryBandLevel.primalAdjacent_limit data level

/--
[PairedBoundaryBandLevel.dual_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma dual_limit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {step : Nat -> Int}
  {data : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {level : PairedBoundaryBandLevel data} :
-- imply
  Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (level.a n) (level.b n) (level.c n) (level.d n))) (muDual.real (Edual.horizontalCrossingEvent (level.a n) (level.b n) (level.c n) (level.d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedBoundaryBandLevel.dual_limit data level

/--
[PairedAdjacentBoundaryBandTransition.local_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma local_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  {muDual : Measure (ConfigSpace (Sym2 W))}
  {step : Nat -> Int}
  {data : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {transition : PairedAdjacentBoundaryBandTransition data} :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n))) (mu.real (E.verticalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)))) atTop (nhds 1) /\ Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n))) (muDual.real (Edual.horizontalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n)))) atTop (nhds 1) /\ Tendsto (fun n => max (muDual.real (Edual.verticalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n))) (muDual.real (Edual.horizontalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandTransition.local_limits data transition

/--
[PairedAdjacentBoundaryBandTransition.false_of_endpoints_and_matched](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_of_endpoints_and_matched_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {step : Nat -> Int}
  {data : PairedAdjacentBoundaryBandScheduleData E Edual mu muDual step}
  {transition : PairedAdjacentBoundaryBandTransition data}
-- given
  (hverticalStart : Tendsto (fun n => mu.real (E.verticalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n))) atTop (nhds 1))
  (hhorizontalEnd : Tendsto (fun n => mu.real (E.horizontalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n))) atTop (nhds 1))
  (hmatchHorizontalLower : forall n, mu.real (E.horizontalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n)) + muDual.real (Edual.verticalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n)) <= 1)
  (hmatchVerticalLower : forall n, mu.real (E.verticalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n)) + muDual.real (Edual.horizontalCrossingEvent (transition.lower.a n) (transition.lower.b n) (transition.lower.c n) (transition.lower.d n)) <= 1)
  (hmatchHorizontalUpper : forall n, mu.real (E.horizontalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)) + muDual.real (Edual.verticalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)) <= 1)
  (hmatchVerticalUpper : forall n, mu.real (E.verticalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)) + muDual.real (Edual.horizontalCrossingEvent (transition.upper.a n) (transition.upper.b n) (transition.upper.c n) (transition.upper.d n)) <= 1) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PairedAdjacentBoundaryBandTransition.false_of_endpoints_and_matched data transition hverticalStart hhorizontalEnd hmatchHorizontalLower hmatchVerticalLower hmatchHorizontalUpper hmatchVerticalUpper

/--
[PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma false_eq_3
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {step pad : Nat -> Int}
  {data : PairedAdjacentOutwardScheduleData D.primalEmbedding D.dualEmbedding mu (D.dualMeasure mu) step pad}
  {transition : D.PaddedPairedAdjacentTransition mu data}
  {B : Real}
-- given
  (hBpos : 0 < B)
  (hBp : forall {x y : V} (hxy : P.graph.Adj x y) (t) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxy t - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x y : W} (hxy : Pdual.graph.Adj x y) (t) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxy t - D.dualEmbedding.vertex x) i| <= B)
  (hpad : forall n, 4 * B <= (pad n : Real))
  (hspanX0 : forall n, transition.a0 n + 5 * B < transition.b0 n - 5 * B)
  (hspanY0 : forall n, transition.c0 n + 5 * B < transition.d0 n - 5 * B)
  (hspanX1 : forall n, transition.a1 n + 5 * B < transition.b1 n - 5 * B)
  (hspanY1 : forall n, transition.c1 n + 5 * B < transition.d1 n - 5 * B) :
-- imply
  False := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.PaddedPairedAdjacentTransition.false D mu data transition B hBpos hBp hBd hpad hspanX0 hspanY0 hspanX1 hspanY1

/--
[PeriodicPlaneEmbedding.deepPreferenceGrid_orbitBox_subset_rect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma deepPreferenceGrid_orbitBox_subset_rect_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {v : PreferenceGridVertex width height}
-- given
  (R M width height margin : Nat)
  (hx : E.orbitBoxCoordinateBound R (0 : Fin 2) <= M + margin)
  (hy : E.orbitBoxCoordinateBound R (1 : Fin 2) <= M + margin)
  (hvLeft : margin <= v.1.val)
  (hvRight : v.1.val + margin < width)
  (hvBottom : margin <= v.2.val)
  (hvTop : v.2.val + margin < height) :
-- imply
  P.shift (preferenceGridSite v) '' (P.orbitBox R : Set V) <= E.rectVertices (-(M : Real)) (M + width : Real) (-(M : Real)) (M + height : Real) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.deepPreferenceGrid_orbitBox_subset_rect E R M width height margin hx hy v hvLeft hvRight hvBottom hvTop

/--
[PeriodicPlaneEmbedding.exists_coupled_endpointCrossings_tendsto_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_coupled_endpointCrossings_tendsto_one_of_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r y B s : Real}
  {t : Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (ht : 3 * B < t)
  (minimumWidth minimumHeight : Nat -> Nat)
  (hminimumWidth : forall n, 3 * B < 3 * (minimumWidth n : Real)) :
-- imply
  exists width height : Nat -> Nat, (forall n, minimumWidth n <= width n) /\ (forall n, minimumHeight n <= height n) /\ Tendsto (fun n => mu.real (E.verticalCrossingEvent r (r + width n) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.horizontalCrossingEvent r (r + width n) y (y + height n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_coupled_endpointCrossings_tendsto_one_of_unique E mu hFKG hTI hunique r y B s hB0 hB t ht minimumWidth minimumHeight hminimumWidth

/--
[PeriodicPlaneEmbedding.exists_dependentSpan_endpointCrossings_tendsto_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_dependentSpan_endpointCrossings_tendsto_one_of_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {r y B s : Real}
  {t : Int}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (ht : 3 * B < t)
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Nat -> Int)
  (hhorizontalSpan : forall n w, minimumWidth n <= w -> 3 * B < horizontalRight n w - horizontalLeft n w) :
-- imply
  exists width height : Nat -> Nat, (forall n, minimumWidth n <= width n) /\ (forall n, minimumHeight n <= height n) /\ Tendsto (fun n => mu.real (E.verticalCrossingEvent r (r + width n) ((2 * s + (s + t)) / 3) ((s + 2 * (s + t)) / 3))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.horizontalCrossingEvent (horizontalLeft n (width n)) (horizontalRight n (width n)) y (y + height n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_dependentSpan_endpointCrossings_tendsto_one_of_unique E mu hFKG hTI hunique r y B s hB0 hB t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[PeriodicPlaneEmbedding.exists_rowwise_dependentSpan_endpointCrossings_tendsto_one_of_unique](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_rowwise_dependentSpan_endpointCrossings_tendsto_one_of_unique_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Real}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |E.coordinates (E.edgeArc hxz u - E.vertex x) i| <= B)
  (r y s : Nat -> Real)
  (t : Nat -> Int)
  (ht : forall n, 3 * B < t n)
  (epsilon : Nat -> Real)
  (hepsilon : forall n, 0 < epsilon n)
  (hepsilon_zero : Tendsto epsilon atTop (nhds 0))
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Nat -> Int)
  (hhorizontalSpan : forall n w, minimumWidth n <= w -> 3 * B < horizontalRight n w - horizontalLeft n w) :
-- imply
  exists width height : Nat -> Nat, (forall n, minimumWidth n <= width n) /\ (forall n, minimumHeight n <= height n) /\ Tendsto (fun n => mu.real (E.verticalCrossingEvent (r n) (r n + width n) ((2 * s n + (s n + t n)) / 3) ((s n + 2 * (s n + t n)) / 3))) atTop (nhds 1) /\ Tendsto (fun n => mu.real (E.horizontalCrossingEvent (horizontalLeft n (width n)) (horizontalRight n (width n)) (y n) (y n + height n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_rowwise_dependentSpan_endpointCrossings_tendsto_one_of_unique E mu hFKG hTI hunique B hB0 hB r y s t ht epsilon hepsilon hepsilon_zero minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[nonempty_dependentRadiusFirstAdjacentEndpointRow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_dependentRadiusFirstAdjacentEndpointRow_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {template : Finset V}
  {step : Int}
  {cutoff : Nat}
  {epsilon : Real}
  {B : Real}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hepsilon : 0 < epsilon)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (r y s : Nat -> Real)
  (t : Nat -> Int)
  (ht : forall radius, 3 * B < t radius)
  (minimumWidth minimumHeight : Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Nat -> Int)
  (hhorizontalSpan : forall radius width, minimumWidth radius <= width -> 3 * B < horizontalRight radius width - horizontalLeft radius width) :
-- imply
  Nonempty (DependentRadiusFirstAdjacentEndpointRow E Edual mu muDual template step cutoff epsilon B r y s t minimumWidth minimumHeight horizontalLeft horizontalRight) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.nonempty_dependentRadiusFirstAdjacentEndpointRow E Edual mu muDual hunique hFKGDual hTIDual huniqueDual template step cutoff epsilon hepsilon B hB0 hB r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {B : Real}
  {initialStep : Int}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hB0 : 0 <= B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (template : Nat -> Finset V)
  (hinitialStep : 0 <= initialStep)
  (r y s : Nat -> Int -> Nat -> Real)
  (t : Nat -> Int -> Nat -> Int)
  (ht : forall n step radius, 3 * B < t n step radius)
  (minimumWidth minimumHeight : Nat -> Int -> Nat -> Nat)
  (horizontalLeft horizontalRight : Nat -> Int -> Nat -> Nat -> Int)
  (hhorizontalSpan : forall n step radius width, minimumWidth n step radius <= width -> 3 * B < horizontalRight n step radius width - horizontalLeft n step radius width) :
-- imply
  let epsilon : Nat -> Real := fun n => 1 / (n + 1 : Real) exists state : Nat -> Int × Nat, exists rows : forall n, DependentRadiusFirstAdjacentEndpointRow E Edual mu muDual (template n) (state n).1 (state n).2 (epsilon n) B (r n (state n).1) (y n (state n).1) (s n (state n).1) (t n (state n).1) (minimumWidth n (state n).1) (minimumHeight n (state n).1) (horizontalLeft n (state n).1) (horizontalRight n (state n).1), state 0 = (initialStep, 0) /\ (forall n, state (n + 1) = (((rows n).height : Int), (rows n).radius + 1)) /\ (forall n, 0 <= (state n).1) /\ Tendsto (fun n => (rows n).radius) atTop atTop /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template n) ((template n).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (state n).1))) (rows n).radius)) atTop (nhds 0)) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (state (n + 1)).1))) (rows (n + 1)).radius)) atTop (nhds 0)) /\ Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (r n (state n).1 (rows n).radius) (r n (state n).1 (rows n).radius + (rows n).width) ((2 * s n (state n).1 (rows n).radius + (s n (state n).1 (rows n).radius + t n (state n).1 (rows n).radius)) / 3) ((s n (state n).1 (rows n).radius + 2 * (s n (state n).1 (rows n).radius + t n (state n).1 (rows n).radius)) / 3))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (horizontalLeft n (state n).1 (rows n).radius (rows n).width) (horizontalRight n (state n).1 (rows n).radius (rows n).width) (y n (state n).1 (rows n).radius) (y n (state n).1 (rows n).radius + (rows n).height))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_recursiveDependentRadiusFirstAdjacentEndpointRows_with_limits E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hB0 hB template initialStep hinitialStep r y s t ht minimumWidth minimumHeight horizontalLeft horizontalRight hhorizontalSpan

/--
[exists_carriedAsymmetricEndpointCoordinates_with_limits](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_carriedAsymmetricEndpointCoordinates_with_limits_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {B : Nat}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG muDual)
  (hTIDual : Pdual.IsTranslationInvariant muDual)
  (huniqueDual : muDual {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hB : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |Edual.coordinates (Edual.edgeArc hxz u - Edual.vertex x) i| <= B)
  (template : Nat -> Finset V) :
-- imply
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1 exists radius width height : Nat -> Nat, Tendsto radius atTop atTop /\ (forall n, 3 * B + 1 <= width n) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (height n)))) (radius (n + 1)))) atTop (nhds 0)) /\ Tendsto (fun n => muDual.real (Edual.verticalCrossingEvent (4 * B) (4 * B + width n) (-4 * B) (targetY n + 4 * B))) atTop (nhds 1) /\ Tendsto (fun n => muDual.real (Edual.horizontalCrossingEvent (-4 * B) (width n + 12 * B) (4 * B) (4 * B + height n))) atTop (nhds 1) /\ (forall n, (0 : Real) + 5 * B < width n + 8 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < targetY n + 4 * B - 5 * B) /\ (forall n, -(4 * B : Real) + 5 * B < width n + 12 * B - 5 * B) /\ (forall n, (0 : Real) + 5 * B < targetY n + height n - 5 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + width n <= width n + 8 * B - 4 * B) /\ (forall n : Nat, (0 : Real) + 4 * B <= 4 * B) /\ (forall n, (4 * B : Real) + height n <= targetY n + height n - 4 * B) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.exists_carriedAsymmetricEndpointCoordinates_with_limits E Edual mu muDual hunique hFKGDual hTIDual huniqueDual B hBpos hB template

/--
[PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_carriedAsymmetricEndpoints_false_of_primal_limit_eq
  [DecidableEq V]
  [DecidableEq W]
  {D : PeriodicPlanarDualPair P Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {B : Nat}
-- given
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (hFKGDual : IsFKG (D.dualMeasure mu))
  (hTIDual : Pdual.IsTranslationInvariant (D.dualMeasure mu))
  (huniqueDual : (D.dualMeasure mu) {eta | Pdual.HasUniqueInfiniteCluster eta} = 1)
  (hBpos : 0 < B)
  (hBp : forall {x z : V} (hxz : P.graph.Adj x z) (u) (i : Fin 2), |D.primalEmbedding.coordinates (D.primalEmbedding.edgeArc hxz u - D.primalEmbedding.vertex x) i| <= B)
  (hBd : forall {x z : W} (hxz : Pdual.graph.Adj x z) (u) (i : Fin 2), |D.dualEmbedding.coordinates (D.dualEmbedding.edgeArc hxz u - D.dualEmbedding.vertex x) i| <= B)
  (template : Nat -> Finset V) :
-- imply
  let targetY : Nat -> Nat := fun n => 20 * B + n + 1 exists radius width height : Nat -> Nat, Tendsto radius atTop atTop /\ (forall n, 3 * B + 1 <= width n) /\ (forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (template (n + 1)) ((template (n + 1)).image (P.shift (preferenceKingOffset (q (n + 1)).2 + if (q (n + 1)).1.val = 0 then 0 else verticalShift (height n)))) (radius (n + 1)))) atTop (nhds 0)) /\ (Tendsto (fun n => max (mu.real (D.primalEmbedding.horizontalCrossingEvent 0 (width n + 8 * B) 0 (targetY n))) (mu.real (D.primalEmbedding.verticalCrossingEvent 0 (width n + 8 * B) 0 (targetY n + height n)))) atTop (nhds 1) -> False) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlanarDualPair.exists_carriedAsymmetricEndpoints_false_of_primal_limit D mu hunique hFKGDual hTIDual huniqueDual B hBpos hBp hBd template

/--
[PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {Edual : PeriodicPlaneEmbedding Pdual}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {muDual : Measure (ConfigSpace (Sym2 W))}
  [IsProbabilityMeasure muDual]
  {family : forall n, E.NormalBoundaryBandFamily mu (P.orbitBox n) (p n)}
  {familyDual : forall n, Edual.NormalBoundaryBandFamily muDual (Pdual.orbitBox n) (pDual n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (hunique : mu {omega | P.HasUniqueInfiniteCluster omega} = 1)
  (p pDual : Nat -> Real)
  (schedule : forall n, PairedAlignedMarginSchedule E Edual (family n) (familyDual n) (fun _ => 0) (fun _ => 0))
  (hp : Tendsto p atTop (nhds 1))
  (hp_le : forall n, p n <= 1) :
-- imply
  exists radius : Nat -> Nat, forall (k extentX extentY : Nat -> Nat) (data : forall n, AlignedExactExtentPairedMixedBoundaryScores E Edual mu muDual (P.orbitBox n) (Pdual.orbitBox n) (p n) (pDual n) (family n) (familyDual n) (schedule n) (k n) (extentX n) (extentY n)), (forall n, PairedAlignedConnectorSlack E Edual (family n) (familyDual n) (schedule n) (max (radius n) n) (k n)) -> Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent 0 (extentX n) 0 (extentY n))) (mu.real (E.verticalCrossingEvent (data n).raw.data.wideLeft (data n).raw.data.wideRight 0 (extentY n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.exists_uniformOrbitBoxMixedRadius_alignedExact_primalLimit E Edual mu muDual hFKG hTI hunique p pDual family familyDual schedule hp hp_le

/--
[PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma primalAdjacent_limit_of_pairMerge_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {data : forall n, E.CommonSquareNormalBoundaryBandData mu (S n) (margin n) (M n) (score n)}
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (S : Nat -> Finset V)
  (margin M width height radius : Nat -> Nat)
  (score : Nat -> Real)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (hwidth : forall n, 2 * margin n < width n)
  (hheight : forall n, 2 * margin n < height n)
  (hscore : Tendsto score atTop (nhds 1))
  (hscore_le : forall n, score n <= 1)
  (htemplateHit : Tendsto (fun n => mu.real (P.setHitsInfinite (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop : Set V))) atTop (nhds 1))
  (hmerge : forall q : Nat -> Fin 2 × (Fin 3 × Fin 3), Tendsto (fun n => mu.real (P.pairMergeErrorUnion (P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop) ((P.fourShiftTemplate (S n) (data n).zLeft (data n).zRight (data n).zBottom (data n).zTop).image (P.shift (preferenceKingOffset (q n).2 + if (q n).1.val = 0 then 0 else verticalShift (step n)))) (radius n))) atTop (nhds 0))
  (hconnector : forall n (v : PreferenceGridVertex (width n) (height n)), margin n <= v.1.val -> v.1.val + margin n < width n -> margin n <= v.2.val -> v.2.val + margin n < height n -> (P.shift (preferenceGridSite v) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (-(M n : Real)) (M n + width n) (-(M n : Real)) (M n + height n)) :
-- imply
  Tendsto (fun n => max (mu.real (E.horizontalCrossingEvent (-(M n : Real)) (M n + width n) (-(M n : Real)) (M n + height n))) (mu.real (E.verticalCrossingEvent (-(M n : Real)) (M n + width n) (-(M n : Real)) (M n + height n + step n)))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.CommonSquareNormalBoundaryBandData.primalAdjacent_limit_of_pairMerge E mu hFKG hTI S margin M width height radius score data step hstep hwidth hheight hscore hscore_le htemplateHit hmerge hconnector

/--
[PeriodicPlaneEmbedding.nonempty_carriedCrossNestedArray_of_alignedSharedLevelSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldPairedRecurrence.lean)
-/
@[path]
private lemma nonempty_carriedCrossNestedArray_of_alignedSharedLevelSteps_eq
  [DecidableEq V]
  [DecidableEq W]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
  {family : forall m, E.NormalBoundaryBandFamily mu (S m) (score m)}
  {steps : forall n, E.AlignedSharedLevelStep mu S score family verticalRequirement horizontalRequirement (state n).1 (state n).2 (scoreEpsilon n) (mergeEpsilon n)}
-- given
  (S : Nat -> Finset V)
  (score : Nat -> Real)
  (verticalRequirement horizontalRequirement : Nat -> Nat -> Nat)
  (state : Nat -> Nat × Nat)
  (K : Nat -> Nat)
  (scoreEpsilon mergeEpsilon : Nat -> Real)
  (hscoreEpsilon : Tendsto scoreEpsilon atTop (nhds 0))
  (hmergeEpsilon : Tendsto mergeEpsilon atTop (nhds 0))
  (hextentK : forall n, (steps n).extent <= K n)
  (hverticalConnector : forall n, (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <= E.rectVertices (-(K n : Real)) (K n) (-(steps n).extent : Real) (steps n).extent)
  (hhorizontalConnector : forall n, (P.orbitBox (P.bufferedRadius (steps n).nextConnector) : Set V) <= E.rectVertices (-(steps n).extent : Real) (steps n).extent (-(K n : Real)) (K n)) :
-- imply
  Nonempty (E.CarriedCrossNestedArray mu) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.nonempty_carriedCrossNestedArray_of_alignedSharedLevelSteps E mu S score family verticalRequirement horizontalRequirement state K scoreEpsilon mergeEpsilon steps hscoreEpsilon hmergeEpsilon hextentK hverticalConnector hhorizontalConnector


-- created on 2026-10-23
