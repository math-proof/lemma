import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicEndpointRangeBound
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[isingFiniteGraphLaplacian_abs_le_four_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRangeBound.lean)
-/
@[path]
private lemma isingFiniteGraphLaplacian_abs_le_four_of_unitRange_eq
  [Fintype V]
  {G : SimpleGraph V}
  {x : V}
-- given
  (f : V -> Real)
  (hcard : Nat.card ↑(G.neighborSet x) <= 4)
  (hrange : forall y, 0 <= f y /\ f y <= 1) :
-- imply
  |isingFiniteGraphLaplacian G f x| <= 4 := by
-- proof
  apply StatMech.Universality.isingFiniteGraphLaplacian_abs_le_four_of_unitRange G f x hcard hrange

/--
[fullSquareVertex_sampledLaplacian_le_four_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRangeBound.lean)
-/
@[path]
private lemma fullSquareVertex_sampledLaplacian_le_four_of_unitRange_eq
  {n : Nat}
-- given
  (embedding : FKIsingSquareFullVertexNode n -> Complex)
  (Phi : Complex -> Complex)
  (hrange : forall x, 0 <= (Phi (embedding x)).im /\ (Phi (embedding x)).im <= 1) :
-- imply
  forall x, |isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => (Phi (embedding y)).im) x| <= 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareVertex_sampledLaplacian_le_four_of_unitRange n embedding Phi hrange

/--
[fullSquareFace_sampledLaplacian_le_four_of_unitRange](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicEndpointRangeBound.lean)
-/
@[path]
private lemma fullSquareFace_sampledLaplacian_le_four_of_unitRange_eq
  {n : Nat}
-- given
  (embedding : FKIsingSquareFullFaceNode n -> Complex)
  (Phi : Complex -> Complex)
  (hrange : forall c, 0 <= (Phi (embedding c)).im /\ (Phi (embedding c)).im <= 1) :
-- imply
  forall c, |isingFiniteGraphLaplacian (fkIsingSquareFullFaceGraph n) (fun d => (Phi (embedding d)).im) c| <= 4 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullSquareFace_sampledLaplacian_le_four_of_unitRange n embedding Phi hrange


-- created on 2026-10-23
