import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingTorusEmbedding.Part3
open Finset Set StatMech StatMech.FrontierA


/--
[isingSiteToDyadicTorus_injectiveOn_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_injectiveOn_box_eq
  {d k R : Nat}
-- given
  (hside : 2 * R < isingDyadicSide k) :
-- imply
  Set.InjOn (isingSiteToDyadicTorus k) (box d R) := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_injectiveOn_box hside

/--
[isingSiteToDyadicTorus_injectiveOn_finset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_injectiveOn_finset_eq
  {d k R : Nat}
  {S : Finset (Site d)}
-- given
  (hS : ↑S ⊆ box d R)
  (hside : 2 * R < isingDyadicSide k) :
-- imply
  Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)) := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_injectiveOn_finset S hS hside

/--
[isingSiteToDyadicTorus_coordShift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_coordShift_eq
  {d k R : Nat}
  {x : Site d}
  {i : Fin d}
  {b : Bool} :
-- imply
  isingSiteToDyadicTorus k (coordShift x i (stepSign b)) = if b then isingSiteToDyadicTorus k x + isingTorusStep i else isingSiteToDyadicTorus k x - isingTorusStep i := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_coordShift x i b

/--
[isingSiteToDyadicTorus_map_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_map_adj_eq
  {d k R : Nat}
  {x y : Site d}
-- given
  (hxy : (hypercubicLattice d).Adj x y) :
-- imply
  (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y) := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_map_adj hxy

/--
[coordShift_mem_box_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma coordShift_mem_box_succ_eq
  {d k R : Nat}
  {x : Site d}
  {i : Fin d}
  {b : Bool}
-- given
  (hx : x ∈ box d R) :
-- imply
  coordShift x i (stepSign b) ∈ box d (R + 1) := by
-- proof
  apply StatMech.FrontierA.coordShift_mem_box_succ hx i b

/--
[isingSiteToDyadicTorus_reflects_adj_on_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_reflects_adj_on_box_eq
  {d k R : Nat}
  {x y : Site d}
-- given
  (hx : x ∈ box d R)
  (hy : y ∈ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hxy : (isingTorusGraph d k).Adj (isingSiteToDyadicTorus k x) (isingSiteToDyadicTorus k y)) :
-- imply
  (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_reflects_adj_on_box hx hy hside hxy

/--
[mem_isingTorusImageFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma mem_isingTorusImageFinset_eq
  {d k R : Nat}
  {S : Finset (Site d)}
  {z : IsingDyadicTorus d k} :
-- imply
  z ∈ isingTorusImageFinset k S ↔ ∃ x ∈ S, isingSiteToDyadicTorus k x = z := by
-- proof
  apply StatMech.FrontierA.mem_isingTorusImageFinset

/--
[isingSiteToDyadicTorus_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingSiteToDyadicTorus_origin_eq
  {d k R : Nat} :
-- imply
  isingSiteToDyadicTorus k (Percolation.origin d) = 0 := by
-- proof
  apply StatMech.FrontierA.isingSiteToDyadicTorus_origin

/--
[zero_mem_isingTorusImageFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma zero_mem_isingTorusImageFinset_eq
  {d k R : Nat}
  {S : Finset (Site d)}
-- given
  (hzero : Percolation.origin d ∈ S) :
-- imply
  (0 : IsingDyadicTorus d k) ∈ isingTorusImageFinset k S := by
-- proof
  apply StatMech.FrontierA.zero_mem_isingTorusImageFinset hzero

/--
[isingTorusImageEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingTorusImageEquiv_apply_eq
  {d k R : Nat}
  {S : Finset (Site d)}
-- given
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (x : {x // x ∈ S}) :
-- imply
  (isingTorusImageEquiv S hinj x).1 = isingSiteToDyadicTorus k x.1 := by
-- proof
  apply StatMech.FrontierA.isingTorusImageEquiv_apply S hinj x

/--
[isingTorusImageEquiv_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingTorusImageEquiv_adj_eq
  {d k R : Nat}
  {S : Finset (Site d)}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hinj : Set.InjOn (isingSiteToDyadicTorus k) (↑S : Set (Site d)))
  (x y : {x // x ∈ S}) :
-- imply
  (graphS d S).Adj x y ↔ ((isingTorusGraph d k).comap (Subtype.val : {z // z ∈ isingTorusImageFinset k S} → IsingDyadicTorus d k)).Adj (isingTorusImageEquiv S hinj x) (isingTorusImageEquiv S hinj y) := by
-- proof
  apply StatMech.FrontierA.isingTorusImageEquiv_adj S hS hside hinj x y

/--
[isingTorus_localizedTwoPoint_eq_freeCorr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingTorus_localizedTwoPoint_eq_freeCorr_eq
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (a b : {x // x ∈ S}) :
-- imply
  twoPointJ (isingTorusGraph d k) beta (couplingIn (unitEdgeCoupling (isingTorusGraph d k)) (isingTorusImageFinset k S)) (isingSiteToDyadicTorus k a.1) (isingSiteToDyadicTorus k b.1) = freeCorr d beta S a b := by
-- proof
  apply StatMech.FrontierA.isingTorus_localizedTwoPoint_eq_freeCorr S hS hside beta a b

/--
[freeCorr_le_isingTorusTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma freeCorr_le_isingTorusTwoPoint_eq
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k)
  (hbeta : 0 ≤ beta)
  (a b : {x // x ∈ S}) :
-- imply
  freeCorr d beta S a b ≤ isingTorusTwoPoint beta (isingSiteToDyadicTorus k a.1) (isingSiteToDyadicTorus k b.1) := by
-- proof
  apply StatMech.FrontierA.freeCorr_le_isingTorusTwoPoint S hS hside beta hbeta a b

/--
[isingTorus_simonConst_image_eq_phiIsing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingTorus_simonConst_image_eq_phiIsing_eq
  {d k R : Nat}
  {S : Finset (Site d)}
  {beta : Real}
-- given
  (hzero : Percolation.origin d ∈ S)
  (hS : (↑S : Set (Site d)) ⊆ box d R)
  (hside : 2 * (R + 1) < isingDyadicSide k) :
-- imply
  simonConst (isingTorusImageFinset k S) (simonWeightPair (isingTorusGraph d k) beta (unitEdgeCoupling (isingTorusGraph d k)) (isingTorusImageFinset k S) 0) (Finset.univ \ isingTorusImageFinset k S) = phiIsing d beta S := by
-- proof
  apply StatMech.FrontierA.isingTorus_simonConst_image_eq_phiIsing S hzero hS hside beta

/--
[isingTorus_susceptibility_eventually_bounded_subcritical](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingTorusEmbedding.lean)
-/
@[path]
private lemma isingTorus_susceptibility_eventually_bounded_subcritical_eq
  {d k R : Nat}
  {beta : Real}
-- given
  (hd : 2 ≤ d)
  (hbeta : 0 ≤ beta)
  (hlt : beta < IsingFK.betaC (Ising.magnetization d)) :
-- imply
  ∃ C : Real, 0 < C ∧ ∀ᶠ k : Nat in Filter.atTop, (∑ z : IsingDyadicTorus d k, isingTorusTwoPoint beta 0 z) ≤ C := by
-- proof
  apply StatMech.FrontierA.isingTorus_susceptibility_eventually_bounded_subcritical hd beta hbeta hlt


-- created on 2026-10-23
