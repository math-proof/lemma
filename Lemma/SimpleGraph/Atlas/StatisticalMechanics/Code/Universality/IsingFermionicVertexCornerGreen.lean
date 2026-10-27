import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicVertexCornerGreen.Part5
open StatMech StatMech.Universality StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm


/--
[fkIsingSquareAvailableNeighbor_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fkIsingSquareAvailableNeighbor_injective_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  Function.Injective (fkIsingSquareAvailableNeighbor n x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareAvailableNeighbor_injective n x

/--
[fkIsingSquareFullVertex_neighborFinset_eq_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fkIsingSquareFullVertex_neighborFinset_eq_available_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
  [Fintype ↑((fkIsingSquareFullVertexGraph n).neighborSet x)] :
-- imply
  (fkIsingSquareFullVertexGraph n).neighborFinset x = Finset.univ.image (fkIsingSquareAvailableNeighbor n x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fkIsingSquareFullVertex_neighborFinset_eq_available n x

/--
[fullVertex_laplacian_eq_sum_available](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertex_laplacian_eq_sum_available_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (F : FKIsingSquareFullVertexNode n -> Real) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x = ∑ d : FKIsingSquareAvailableDirection n x, (F (fkIsingSquareAvailableNeighbor n x d) - F x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertex_laplacian_eq_sum_available n F x

/--
[fullVertex_laplacian_eq_directionIncrements](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertex_laplacian_eq_directionIncrements_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (F : FKIsingSquareFullVertexNode n -> Real) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) F x = fullVertexDirectionIncrement n F x .east + fullVertexDirectionIncrement n F x .north + fullVertexDirectionIncrement n F x .west + fullVertexDirectionIncrement n F x .south := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertex_laplacian_eq_directionIncrements n F x

/--
[fullVertexColumnIndex_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_coe_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  (fullVertexColumnIndex n x : Int) = x.1 0 + (n : Int) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_coe n x

/--
[fullVertexRowIndex_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_coe_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  (fullVertexRowIndex n x : Int) = x.1 1 + (n : Int) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_coe n x

/--
[fullVertexColumnIndex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_le_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  fullVertexColumnIndex n x <= 2 * n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_le n x

/--
[fullVertexRowIndex_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_le_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  fullVertexRowIndex n x <= 2 * n := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_le n x

/--
[fullVertexColumnIndex_neighbor_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_neighbor_east_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .east) :
-- imply
  fullVertexColumnIndex n (fkIsingSquareNeighbor n x .east h) = fullVertexColumnIndex n x + 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_neighbor_east n x h

/--
[fullVertexColumnIndex_neighbor_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_neighbor_west_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .west) :
-- imply
  fullVertexColumnIndex n (fkIsingSquareNeighbor n x .west h) = fullVertexColumnIndex n x - 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_neighbor_west n x h

/--
[fullVertexColumnIndex_neighbor_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_neighbor_north_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .north) :
-- imply
  fullVertexColumnIndex n (fkIsingSquareNeighbor n x .north h) = fullVertexColumnIndex n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_neighbor_north n x h

/--
[fullVertexColumnIndex_neighbor_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnIndex_neighbor_south_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  fullVertexColumnIndex n (fkIsingSquareNeighbor n x .south h) = fullVertexColumnIndex n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnIndex_neighbor_south n x h

/--
[fullVertexRowIndex_neighbor_north](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_neighbor_north_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .north) :
-- imply
  fullVertexRowIndex n (fkIsingSquareNeighbor n x .north h) = fullVertexRowIndex n x + 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_neighbor_north n x h

/--
[fullVertexRowIndex_neighbor_south](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_neighbor_south_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .south) :
-- imply
  fullVertexRowIndex n (fkIsingSquareNeighbor n x .south h) = fullVertexRowIndex n x - 1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_neighbor_south n x h

/--
[fullVertexRowIndex_neighbor_east](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_neighbor_east_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .east) :
-- imply
  fullVertexRowIndex n (fkIsingSquareNeighbor n x .east h) = fullVertexRowIndex n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_neighbor_east n x h

/--
[fullVertexRowIndex_neighbor_west](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowIndex_neighbor_west_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (h : fkIsingSquareDirectionAvailable n x .west) :
-- imply
  fullVertexRowIndex n (fkIsingSquareNeighbor n x .west h) = fullVertexRowIndex n x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowIndex_neighbor_west n x h

/--
[fullVertexColumnFunction_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexColumnFunction_laplacian_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (F : Nat -> Real)
  (hleft : -(n : Int) < x.1 0) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => F (fullVertexColumnIndex n y)) x = if x.1 0 = (n : Int) then F (fullVertexColumnIndex n x - 1) - F (fullVertexColumnIndex n x) else F (fullVertexColumnIndex n x + 1) + F (fullVertexColumnIndex n x - 1) - 2 * F (fullVertexColumnIndex n x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexColumnFunction_laplacian n F x hleft

/--
[fullVertexRowFunction_laplacian](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexRowFunction_laplacian_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (F : Nat -> Real)
  (hn : 0 < n) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (fun y => F (fullVertexRowIndex n y)) x = if x.1 1 = -(n : Int) then F (fullVertexRowIndex n x + 1) - F (fullVertexRowIndex n x) else if x.1 1 = (n : Int) then F (fullVertexRowIndex n x - 1) - F (fullVertexRowIndex n x) else F (fullVertexRowIndex n x + 1) + F (fullVertexRowIndex n x - 1) - 2 * F (fullVertexRowIndex n x) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexRowFunction_laplacian n F x hn

/--
[fullVertexGhostRate_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertexGhostRate_split_eq
  {n : Nat}
  {x : FKIsingSquareFullVertexNode n} :
-- imply
  isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x + isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x = isingFermionicGhostRate (fkIsingSquareFullVertexGhostMultiplicity n) x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertexGhostRate_split n x

/--
[vertexLeftColumnCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexLeftColumnCap_nonneg_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n} :
-- imply
  0 <= vertexLeftColumnCap source x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexLeftColumnCap_nonneg source x

/--
[vertexBottomRowRobinCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexBottomRowRobinCap_nonneg_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n} :
-- imply
  0 <= vertexBottomRowRobinCap source x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBottomRowRobinCap_nonneg source x

/--
[isingNatReverseCappedRobinTent_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma isingNatReverseCappedRobinTent_nonneg_eq
  {coefficient : Real}
  {top source i : Nat}
-- given
  (hcoefficient : 0 < coefficient) :
-- imply
  0 <= isingNatReverseCappedRobinTent coefficient top source i := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingNatReverseCappedRobinTent_nonneg coefficient hcoefficient top source i

/--
[vertexTopRowRobinCap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexTopRowRobinCap_nonneg_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n} :
-- imply
  0 <= vertexTopRowRobinCap n source x := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexTopRowRobinCap_nonneg n source x

/--
[isingNatReverseCappedRobinTent_secondDifference_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma isingNatReverseCappedRobinTent_secondDifference_nonpos_eq
  {coefficient : Real}
  {top source i : Nat}
-- given
  (hi : 0 < i)
  (hitop : i < top) :
-- imply
  isingNatReverseCappedRobinTent coefficient top source (i + 1) + isingNatReverseCappedRobinTent coefficient top source (i - 1) - 2 * isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingNatReverseCappedRobinTent_secondDifference_nonpos coefficient top source i hi hitop

/--
[isingNatReverseCappedRobinTent_secondDifference_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma isingNatReverseCappedRobinTent_secondDifference_source_eq
  {coefficient : Real}
  {top source : Nat}
-- given
  (hsource : 0 < source)
  (hsourceTop : source < top) :
-- imply
  isingNatReverseCappedRobinTent coefficient top source (source + 1) + isingNatReverseCappedRobinTent coefficient top source (source - 1) - 2 * isingNatReverseCappedRobinTent coefficient top source source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingNatReverseCappedRobinTent_secondDifference_source coefficient top source hsource hsourceTop

/--
[isingNatReverseCappedRobinTent_right_balance](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma isingNatReverseCappedRobinTent_right_balance_eq
  {coefficient : Real}
  {top source : Nat}
-- given
  (hcoefficient : 0 < coefficient)
  (hsourceTop : source < top) :
-- imply
  isingNatReverseCappedRobinTent coefficient top source (top - 1) - isingNatReverseCappedRobinTent coefficient top source top - coefficient * isingNatReverseCappedRobinTent coefficient top source top = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingNatReverseCappedRobinTent_right_balance coefficient hcoefficient top source hsourceTop

/--
[isingNatReverseCappedRobinTent_successor_sub_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma isingNatReverseCappedRobinTent_successor_sub_nonpos_eq
  {coefficient : Real}
  {top source i : Nat} :
-- imply
  isingNatReverseCappedRobinTent coefficient top source (i + 1) - isingNatReverseCappedRobinTent coefficient top source i <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.isingNatReverseCappedRobinTent_successor_sub_nonpos coefficient top source i

/--
[vertexLeftColumnCap_modifiedLaplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexLeftColumnCap_modifiedLaplacian_nonpos_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hx : Not (fkIsingSquareFullVertexFixedBoundary n x)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexLeftColumnCap source) x - isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) x * vertexLeftColumnCap source x <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexLeftColumnCap_modifiedLaplacian_nonpos n source x hx

/--
[vertexLeftColumnCap_modifiedLaplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexLeftColumnCap_modifiedLaplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullVertexNode n}
-- given
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexLeftColumnCap source) source - isingFermionicGhostRate (fullVertexRightGhostMultiplicity n) source * vertexLeftColumnCap source source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexLeftColumnCap_modifiedLaplacian_source n source hfixed hright

/--
[vertexBottomRowRobinCap_modifiedLaplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexBottomRowRobinCap_modifiedLaplacian_nonpos_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hsourceBottom : -(n : Int) < source.1 1) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexBottomRowRobinCap source) x - isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x * vertexBottomRowRobinCap source x <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBottomRowRobinCap_modifiedLaplacian_nonpos n source x hn hsourceBottom

/--
[vertexBottomRowRobinCap_modifiedLaplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexBottomRowRobinCap_modifiedLaplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexBottomRowRobinCap source) source - isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source * vertexBottomRowRobinCap source source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexBottomRowRobinCap_modifiedLaplacian_source n source hn hbottom htop

/--
[vertexTopRowRobinCap_modifiedLaplacian_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexTopRowRobinCap_modifiedLaplacian_nonpos_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hsourceTop : source.1 1 < (n : Int)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexTopRowRobinCap n source) x - isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) x * vertexTopRowRobinCap n source x <= 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexTopRowRobinCap_modifiedLaplacian_nonpos n source x hn hsourceTop

/--
[vertexTopRowRobinCap_modifiedLaplacian_source](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexTopRowRobinCap_modifiedLaplacian_source_eq
  {n : Nat}
  {source : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int)) :
-- imply
  isingFiniteGraphLaplacian (fkIsingSquareFullVertexGraph n) (vertexTopRowRobinCap n source) source - isingFermionicGhostRate (fullVertexVerticalGhostMultiplicity n) source * vertexTopRowRobinCap n source source = -1 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexTopRowRobinCap_modifiedLaplacian_source n source hn hbottom htop

/--
[fullVertex_adj_columnIndex_eq_or_rowIndex_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma fullVertex_adj_columnIndex_eq_or_rowIndex_eq_eq
  {n : Nat}
  {x y : FKIsingSquareFullVertexNode n}
-- given
  (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
-- imply
  fullVertexColumnIndex n x = fullVertexColumnIndex n y ∨ fullVertexRowIndex n x = fullVertexRowIndex n y := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.fullVertex_adj_columnIndex_eq_or_rowIndex_eq n x y hxy

/--
[vertexLowerCornerCaps_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexLowerCornerCaps_edgewise_eq
  {n : Nat}
  {source x y : FKIsingSquareFullVertexNode n}
-- given
  (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
-- imply
  (vertexLeftColumnCap source y - vertexLeftColumnCap source x) * (vertexBottomRowRobinCap source y - vertexBottomRowRobinCap source x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexLowerCornerCaps_edgewise n source x y hxy

/--
[vertexUpperCornerCaps_edgewise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexUpperCornerCaps_edgewise_eq
  {n : Nat}
  {source x y : FKIsingSquareFullVertexNode n}
-- given
  (hxy : (fkIsingSquareFullVertexGraph n).Adj x y) :
-- imply
  (vertexLeftColumnCap source y - vertexLeftColumnCap source x) * (vertexTopRowRobinCap n source y - vertexTopRowRobinCap n source x) = 0 := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexUpperCornerCaps_edgewise n source x y hxy

/--
[vertexPointPoissonBarrier_le_lowerLeftProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_lowerLeftProduct_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int)) :
-- imply
  vertexPointPoissonBarrier n (some source) (some x) <= vertexLeftColumnCap source x * vertexBottomRowRobinCap source x / (vertexLeftColumnCap source source + vertexBottomRowRobinCap source source) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_lowerLeftProduct n source x hn hfixed hright hbottom htop

/--
[vertexPointPoissonBarrier_le_upperLeftProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_upperLeftProduct_eq
  {n : Nat}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int)) :
-- imply
  vertexPointPoissonBarrier n (some source) (some x) <= vertexLeftColumnCap source x * vertexTopRowRobinCap n source x / (vertexLeftColumnCap source source + vertexTopRowRobinCap n source source) := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_upperLeftProduct n source x hn hfixed hright hbottom htop

/--
[vertexMarkedEndpointLayer_coordinate_cases](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexMarkedEndpointLayer_coordinate_cases_eq
  {n radius : Nat}
  {x : FKIsingSquareFullVertexNode n}
-- given
  (hx : vertexMarkedEndpointLayer n radius (some x)) :
-- imply
  fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius ∨ fullVertexColumnIndex n x + (2 * n - fullVertexRowIndex n x) <= radius := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexMarkedEndpointLayer_coordinate_cases n radius x hx

/--
[vertexPointPoissonBarrier_le_lowerLeftRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_lowerLeftRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int))
  (hcorner : fullVertexColumnIndex n x + fullVertexRowIndex n x <= radius)
  (hdistance : 0 < distance)
  (hsourceDistance : distance <= (fullVertexColumnIndex n source : Real) + (fullVertexRowIndex n source : Real) + 1 / isingFermionicGhostCoefficient) :
-- imply
  vertexPointPoissonBarrier n (some source) (some x) <= (radius : Real) * ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_lowerLeftRadius n radius distance source x hn hfixed hright hbottom htop hcorner hdistance hsourceDistance

/--
[vertexPointPoissonBarrier_le_upperLeftRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_upperLeftRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int))
  (hcorner : fullVertexColumnIndex n x + (2 * n - fullVertexRowIndex n x) <= radius)
  (hdistance : 0 < distance)
  (hsourceDistance : distance <= (fullVertexColumnIndex n source : Real) + (2 * n - fullVertexRowIndex n source : Nat) + 1 / isingFermionicGhostCoefficient) :
-- imply
  vertexPointPoissonBarrier n (some source) (some x) <= (radius : Real) * ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_upperLeftRadius n radius distance source x hn hfixed hright hbottom htop hcorner hdistance hsourceDistance

/--
[vertexPointPoissonBarrier_le_markedEndpointRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_markedEndpointRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source x : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int))
  (hx : vertexMarkedEndpointLayer n radius (some x))
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (fullVertexColumnIndex n source : Real) + (fullVertexRowIndex n source : Real) + 1 / isingFermionicGhostCoefficient)
  (hupperDistance : distance <= (fullVertexColumnIndex n source : Real) + (2 * n - fullVertexRowIndex n source : Nat) + 1 / isingFermionicGhostCoefficient) :
-- imply
  vertexPointPoissonBarrier n (some source) (some x) <= (radius : Real) * ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_markedEndpointRadius n radius distance source x hn hfixed hright hbottom htop hx hdistance hlowerDistance hupperDistance

/--
[vertexPointPoissonBarrier_le_exceptionalSourceRadius](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicVertexCornerGreen.lean)
-/
@[path]
private lemma vertexPointPoissonBarrier_le_exceptionalSourceRadius_eq
  {n radius : Nat}
  {distance : Real}
  {source : FKIsingSquareFullVertexNode n}
-- given
  (hn : 0 < n)
  (hfixed : Not (fkIsingSquareFullVertexFixedBoundary n source))
  (hright : source.1 0 < (n : Int))
  (hbottom : -(n : Int) < source.1 1)
  (htop : source.1 1 < (n : Int))
  (hdistance : 0 < distance)
  (hlowerDistance : distance <= (fullVertexColumnIndex n source : Real) + (fullVertexRowIndex n source : Real) + 1 / isingFermionicGhostCoefficient)
  (hupperDistance : distance <= (fullVertexColumnIndex n source : Real) + (2 * n - fullVertexRowIndex n source : Nat) + 1 / isingFermionicGhostCoefficient) :
-- imply
  forall z, z ∈ isingFiniteWeightedInteriorExceptionalSources (vertexDirichletBoundary n) (vertexMarkedEndpointLayer n radius) -> vertexPointPoissonBarrier n (some source) z <= (radius : Real) * ((radius : Real) + 1 / isingFermionicGhostCoefficient) / distance := by
-- proof
  apply StatMech.Universality.FKIsingSquareBoundaryLayerCoordinateOneForm.vertexPointPoissonBarrier_le_exceptionalSourceRadius n radius distance source hn hfixed hright hbottom htop hdistance hlowerDistance hupperDistance


-- created on 2026-10-23
