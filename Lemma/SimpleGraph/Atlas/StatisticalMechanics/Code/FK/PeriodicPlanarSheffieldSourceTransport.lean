import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldSourceTransport
open Filter MeasureTheory Set Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_transport_tendsto_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldSourceTransport.lean)
-/
@[path]
private lemma adjacentHeightVerticalCrossing_transport_tendsto_one_eq
  [DecidableEq V]
  [Countable V]
  {E : PeriodicPlaneEmbedding P}
  {mu : Measure (ConfigSpace (Sym2 V))}
  [IsProbabilityMeasure mu]
-- given
  (hFKG : IsFKG mu)
  (hTI : P.IsTranslationInvariant mu)
  (a b c d : Nat -> Real)
  (step : Nat -> Int)
  (hstep : forall n, 0 <= step n)
  (L R : Nat -> Finset V)
  (z : Nat -> Site 2)
  (radius : Nat -> Nat)
  (epsilon : Nat -> Real)
  (hbottom : Tendsto (fun n => mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((L n).image (P.shift (z n)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n)))) atTop (nhds 1))
  (hhit : Tendsto (fun n => mu.real (P.setHitsInfinite (R n : Set V))) atTop (nhds 1))
  (hepsilon : Tendsto epsilon atTop (nhds 0))
  (hopposite : forall n, mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((R n).image (P.shift (z n)) : Set V) (E.rectBottomBoundaryVertices (a n) (b n) (c n) (d n))) <= mu.real (E.rectSideConnectionEvent (a n) (b n) (c n) (d n) ((R n).image (P.shift (z n)) : Set V) (E.rectTopBoundaryVertices (a n) (b n) (c n) (d n))) + epsilon n)
  (hmergeCurrent : Tendsto (fun n => mu.real (P.pairMergeErrorUnion (L n) (R n) (radius n))) atTop (nhds 0))
  (hmergeSuccessor : Tendsto (fun n => mu.real (P.pairMergeErrorUnion (L n) ((R n).image (P.shift (verticalShift (step n)))) (radius n))) atTop (nhds 0))
  (hconnector : forall n, (P.shift (z n) '' (P.orbitBox (P.bufferedRadius (radius n)) : Set V)) <= E.rectVertices (a n) (b n) (c n) (d n)) :
-- imply
  Tendsto (fun n => mu.real (E.verticalCrossingEvent (a n) (b n) (c n) (d n + step n))) atTop (nhds 1) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.adjacentHeightVerticalCrossing_transport_tendsto_one E mu hFKG hTI a b c d step hstep L R z radius epsilon hbottom hhit hepsilon hopposite hmergeCurrent hmergeSuccessor hconnector


-- created on 2026-10-23
