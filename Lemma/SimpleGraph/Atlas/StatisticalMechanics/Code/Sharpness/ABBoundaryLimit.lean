import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.ABBoundaryLimit.Part4
open Filter Finset MeasureTheory Set SimpleGraph Topology StatMech StatMech.Sharpness


/--
[abbl_abbEdgeEquiv_symm_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_abbEdgeEquiv_symm_mk_eq
  {sigma : U ≃ W}
  {a b : W} :
-- imply
  (abbEdgeEquiv sigma).symm s(a, b) = s(sigma.symm a, sigma.symm b) := by
-- proof
  apply StatMech.Sharpness.abbl_abbEdgeEquiv_symm_mk sigma a b

/--
[abbl_residual_le_exp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_residual_le_exp_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {J : Sym2 V → Real}
  {o : V}
  {k : Nat}
  {R : Set (ConfigSpace (Sym2 (Option V)))}
-- given
  (beta h : Real)
  (hJ : ∀ e ∈ G.edgeFinset, 0 ≤ J e)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h)
  (hRghost : R ⊆ (connEvent (withGhost G) Set.univ (some o) {none})ᶜ)
  (hcard : ∀ eta : {e // e ∉ FieldGhostDict.ghostEdges V} → Bool, ∀ gamma : {e // e ∈ FieldGhostDict.ghostEdges V} → Bool, abgrMerge (FieldGhostDict.ghostEdges V) gamma eta ∈ R → k ≤ (abgrActiveGhost G o eta).card) :
-- imply
  probV (abfaParams G J beta h) R ≤ Real.exp (-(h * (k : Real))) := by
-- proof
  apply StatMech.Sharpness.abbl_residual_le_exp G J o beta h hJ hbeta hh k R hRghost hcard

/--
[abbl_closeGhost_conn_of_not_ghost](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_closeGhost_conn_of_not_ghost_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {o y : V}
  {omega : ConfigSpace (Sym2 (Option V))}
-- given
  (hconn : omega ∈ connEvent (withGhost G) Set.univ (some o) {some y})
  (hnot : omega ∉ connEvent (withGhost G) Set.univ (some o) {none}) :
-- imply
  abgrCloseGhost omega ∈ connEvent (withGhost G) Set.univ (some o) {some y} := by
-- proof
  apply StatMech.Sharpness.abbl_closeGhost_conn_of_not_ghost G o y omega hconn hnot

/--
[abbl_le_l1dist_origin_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_le_l1dist_origin_of_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {y : Site d}
-- given
  (hn : 0 < n)
  (hy : y ∈ vertexBoundary d n) :
-- imply
  n ≤ l1dist d (origin d) y := by
-- proof
  apply StatMech.Sharpness.abbl_le_l1dist_origin_of_boundary G hn hy

/--
[abbl_activeGhost_card_ge_of_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_activeGhost_card_ge_of_boundary_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {y : sctBox d n}
-- given
  (hn : 0 < n)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
  (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
  (hy : (y : Site d) ∈ vertexBoundary d n)
  (hconn : abgrCloseGhost (abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta) ∈ connEvent (withGhost (sctBoxGraph d n)) Set.univ (some (sctBoxOrigin d n)) {some y}) :
-- imply
  n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n) (sctBoxOrigin d n) eta).card := by
-- proof
  apply StatMech.Sharpness.abbl_activeGhost_card_ge_of_boundary G hn eta gamma y hy hconn

/--
[abbl_residual_activeGhost_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_residual_activeGhost_card_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
-- given
  (hn : 0 < n)
  (eta : {e // e ∉ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
  (gamma : {e // e ∈ FieldGhostDict.ghostEdges (sctBox d n)} → Bool)
  (hres : abgrMerge (FieldGhostDict.ghostEdges (sctBox d n)) gamma eta ∈ abblResidualEvent d n) :
-- imply
  n + 1 ≤ (abgrActiveGhost (sctBoxGraph d n) (sctBoxOrigin d n) eta).card := by
-- proof
  apply StatMech.Sharpness.abbl_residual_activeGhost_card G hn eta gamma hres

/--
[abbl_residual_prob_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_residual_prob_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
-- given
  (hn : 0 < n)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  probV (abfaParams (sctBoxGraph d n) (abbCoupling d n) beta h) (abblResidualEvent d n) ≤ Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
-- proof
  apply StatMech.Sharpness.abbl_residual_prob_le G hn beta h hbeta hh

/--
[abbl_abfaMag_le_abbMag_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_abfaMag_le_abbMag_le_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
-- given
  (hn : 0 < n)
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  abfaMag (sctBoxGraph d n) (abbCoupling d n) (sctBoxOrigin d n) beta h ≤ abbMag d n beta h ∧ abbMag d n beta h ≤ abfaMag (sctBoxGraph d n) (abbCoupling d n) (sctBoxOrigin d n) beta h + Real.exp (-(h * ((n + 1 : Nat) : Real))) := by
-- proof
  apply StatMech.Sharpness.abbl_abfaMag_le_abbMag_le G hn beta h hbeta hh

/--
[abbl_abfaMag_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_abfaMag_relabel_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  [Fintype U]
  [DecidableEq U]
  [Fintype W]
  [DecidableEq W]
  {G : SimpleGraph U}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {sigma : U ≃ W}
  {J : Sym2 U → Real}
  {K : Sym2 W → Real}
  {o : U}
-- given
  (hgraph : ∀ x y, G.Adj x y ↔ H.Adj (sigma x) (sigma y))
  (hcoupling : ∀ x y, G.Adj x y → J s(x, y) = K s(sigma x, sigma y))
  (beta h : Real) :
-- imply
  abfaMag G J o beta h = abfaMag H K (sigma o) beta h := by
-- proof
  apply StatMech.Sharpness.abbl_abfaMag_relabel G G H sigma hgraph J K hcoupling o beta h

/--
[abblLatticeCoupling_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abblLatticeCoupling_mk_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {x y : Site d} :
-- imply
  abblLatticeCoupling d s(x, y) = if (hypercubicLattice d).Adj x y then 1 else 0 := by
-- proof
  apply StatMech.Sharpness.abblLatticeCoupling_mk G d x y

/--
[abblLatticeCoupling_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abblLatticeCoupling_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {e : Sym2 (Site d)} :
-- imply
  0 ≤ abblLatticeCoupling d e := by
-- proof
  apply StatMech.Sharpness.abblLatticeCoupling_nonneg G d e

/--
[abblLatticeCoupling_support](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abblLatticeCoupling_support_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
  {x y : Site d}
-- given
  (hxy : ¬ (hypercubicLattice d).Adj x y) :
-- imply
  abblLatticeCoupling d s(x, y) = 0 := by
-- proof
  apply StatMech.Sharpness.abblLatticeCoupling_support G x y hxy

/--
[abblBoxEquiv_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abblBoxEquiv_val_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
  {x : sctBox d n} :
-- imply
  ((abblBoxEquiv d n x : ↑(ablBoxFinset d n)) : Site d) = x := by
-- proof
  apply StatMech.Sharpness.abblBoxEquiv_val G d n x

/--
[abblBoxEquiv_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abblBoxEquiv_origin_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat} :
-- imply
  abblBoxEquiv d n (sctBoxOrigin d n) = ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ := by
-- proof
  apply StatMech.Sharpness.abblBoxEquiv_origin G d n

/--
[abbl_abfaMag_eq_window](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_abfaMag_eq_window_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
-- given
  (beta h : Real) :
-- imply
  abfaMag (sctBoxGraph d n) (abbCoupling d n) (sctBoxOrigin d n) beta h = abfaMag (abigWindowGraph (hypercubicLattice d) (ablBoxFinset d n)) (abigWindowCoupling (abblLatticeCoupling d) (ablBoxFinset d n)) ⟨(0 : Site d), zero_mem_ablBoxFinset d n⟩ beta h := by
-- proof
  apply StatMech.Sharpness.abbl_abfaMag_eq_window G d n beta h

/--
[abbl_finiteGhost_eq_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_finiteGhost_eq_ambient_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d n : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  abfaMag (sctBoxGraph d n) (abbCoupling d n) (sctBoxOrigin d n) beta h = (abigMeasure (abblLatticeCoupling d) beta h).real (connEvent (withGhost (hypercubicLattice d)) (abigGhostWindow (ablBoxFinset d n) : Set (Option (Site d))) (some (origin d)) {none}) := by
-- proof
  apply StatMech.Sharpness.abbl_finiteGhost_eq_ambient G beta h hbeta hh

/--
[abbl_tendsto_finiteGhost_shiftedBase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_tendsto_finiteGhost_shiftedBase_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 ≤ h) :
-- imply
  Tendsto (fun n ↦ abfaMag (sctBoxGraph d n) (abbCoupling d n) (sctBoxOrigin d n) beta h) atTop (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h)) := by
-- proof
  apply StatMech.Sharpness.abbl_tendsto_finiteGhost_shiftedBase G d beta h hbeta hh

/--
[abbl_tendsto_boundaryError_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_tendsto_boundaryError_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
-- given
  (h : Real)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n : Nat ↦ Real.exp (-(h * (((n + 2 : Nat) : Real))))) atTop (nhds 0) := by
-- proof
  apply StatMech.Sharpness.abbl_tendsto_boundaryError_zero G h hh

/--
[abbl_tendsto_abbMag_shifted](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/ABBoundaryLimit.lean)
-/
@[path]
private lemma abbl_tendsto_abbMag_shifted_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {d : Nat}
-- given
  (beta h : Real)
  (hbeta : 0 ≤ beta)
  (hh : 0 < h) :
-- imply
  Tendsto (fun n ↦ abbMag d (n + 1) beta h) atTop (nhds (abigMag (hypercubicLattice d) (abblLatticeCoupling d) (0 : Site d) beta h)) := by
-- proof
  apply StatMech.Sharpness.abbl_tendsto_abbMag_shifted G d beta h hbeta hh


-- created on 2026-10-23
