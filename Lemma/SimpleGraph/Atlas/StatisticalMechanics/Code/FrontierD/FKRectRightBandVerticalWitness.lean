import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.FKRectRightBandVerticalWitness.Part3
open SimpleGraph StatMech StatMech.FrontierD


/--
[fkRectRightStripBand_connection_reachable_verticalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectRightStripBand_connection_reachable_verticalCut_eq
  {R : FKRectTorus}
  {cut lower upper : Nat}
  {omega : R.Configuration}
  {x y : FKRectRightStripBandVertex R cut lower upper}
-- given
  (hlower : 1 ≤ lower)
  (hxy : FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut lower upper → R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ FK.connEvent (fkRectInducedGraph R (fkRectRightStripBand R cut lower upper)) x y) :
-- imply
  (fkRectVerticalCutGraph R omega).Reachable x.1 y.1 := by
-- proof
  apply StatMech.FrontierD.fkRectRightStripBand_connection_reachable_verticalCut R cut lower upper hlower omega x y hxy

/--
[fkRectVerticalSeamEdgeAt_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectVerticalSeamEdgeAt_indexedEdge_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x) = s(fkRectRowZeroVertex R x, fkRectLastRowVertex R x) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamEdgeAt_indexedEdge R x

/--
[fkRectRowZeroAttachmentEdgeAt_indexedEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectRowZeroAttachmentEdgeAt_indexedEdge_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  fkRectTorusIndexedEdge R (fkRectRowZeroAttachmentEdgeAt R x) = s(fkRectRowOneVertex R x, fkRectRowZeroVertex R x) := by
-- proof
  apply StatMech.FrontierD.fkRectRowZeroAttachmentEdgeAt_indexedEdge R x

/--
[fkRectVerticalSeamEdgeAt_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectVerticalSeamEdgeAt_crosses_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R (fkRectVerticalSeamEdgeAt R x)) := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalSeamEdgeAt_crosses R x

/--
[fkRectRowZeroAttachmentEdgeAt_not_crosses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectRowZeroAttachmentEdgeAt_not_crosses_eq
  {R : FKRectTorus}
  {x : Fin R.width} :
-- imply
  ¬ fkRectCrossesVerticalSeam R (fkRectTorusIndexedEdge R (fkRectRowZeroAttachmentEdgeAt R x)) := by
-- proof
  apply StatMech.FrontierD.fkRectRowZeroAttachmentEdgeAt_not_crosses R x

/--
[fkRectRightBand_chain_reachable_verticalCut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectRightBand_chain_reachable_verticalCut_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {omega : R.Configuration}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hx : cut ≤ x.val)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t)
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectRightStripBand R cut 1 (R.height - 1)) t) :
-- imply
  (fkRectVerticalCutGraph R omega).Reachable (fkRectRowOneVertex R x) (fkRectLastRowVertex R x) := by
-- proof
  apply StatMech.FrontierD.fkRectRightBand_chain_reachable_verticalCut R cut x hx omega t hpair hchain

/--
[fkRectVerticalWindingEvent_of_rightBand_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKRectRightBandVerticalWitness.lean)
-/
@[path]
private lemma fkRectVerticalWindingEvent_of_rightBand_chain_eq
  {R : FKRectTorus}
  {cut : Nat}
  {x : Fin R.width}
  {omega : R.Configuration}
  {t : Finset (FKRectRightStripBandVertex R cut 1 (R.height - 1) × FKRectRightStripBandVertex R cut 1 (R.height - 1))}
-- given
  (hx : cut ≤ x.val)
  (hpair : (fkRectRightBandRowOne R cut x hx, fkRectRightBandLastRow R cut x hx) ∈ t)
  (hchain : FK.ocd_innerRestrict (Subtype.val : FKRectRightStripBandVertex R cut 1 (R.height - 1) → R.Vertex) (fkRectFullGraphConfiguration R omega) ∈ fkRectInducedConnectionChainEvent R (fkRectRightStripBand R cut 1 (R.height - 1)) t)
  (hseam : omega (fkRectVerticalSeamEdgeAt R x) = true)
  (hattach : omega (fkRectRowZeroAttachmentEdgeAt R x) = true) :
-- imply
  omega ∈ fkRectVerticalWindingEvent R := by
-- proof
  apply StatMech.FrontierD.fkRectVerticalWindingEvent_of_rightBand_chain R cut x hx omega t hpair hchain hseam hattach


-- created on 2026-10-23
