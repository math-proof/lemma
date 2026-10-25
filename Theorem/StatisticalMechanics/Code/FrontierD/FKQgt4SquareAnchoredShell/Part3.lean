/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/FKQgt4SquareAnchoredShell.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4SquareBoxClusterUnion
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4CriticalFreeShellSummability
import Theorem.StatisticalMechanics.Code.FrontierD.FKQgt4WiredPhaseInput.Part2
import Theorem.StatisticalMechanics.Code.Universality.FrameChangeIso.Part8
import Theorem.StatisticalMechanics.Code.Lattice.EnclosingLength.Part2
import Theorem.StatisticalMechanics.Code.Lattice.LeftFace.Part4
import Def.StatisticalMechanics.Code.FrontierD.FKQgt4SquareAnchoredShell.Part3
open Filter MeasureTheory Set SimpleGraph


namespace StatMech.FrontierD

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

open StatMech.Universality

noncomputable section

theorem measurableSet_fkQgt4CriticalFreeSphereConnectionEvent (j : Nat) :
    MeasurableSet (fkQgt4CriticalFreeSphereConnectionEvent j) := by
  unfold fkQgt4CriticalFreeSphereConnectionEvent
  exact MeasurableSet.biUnion (fkQgt4SiteSphere j).countable_toSet
    (fun x _ => measurableSet_connected (origin 2) x)

theorem fkQgt4AxisAnchoredSphereConnectionEvent_measure_eq
    (mu : Measure (ConfigSpace (Sym2 (Site 2))))
    (htrans : ConfigSpace.IsTranslationInvariant
      (G := Multiplicative (Site 2)) mu) (j : Nat) :
    mu (fkQgt4AxisAnchoredSphereConnectionEvent j) =
      mu (fkQgt4CriticalFreeSphereConnectionEvent j) := by
  exact htrans.measure_preimage (axisToOriginShift j)
    (measurableSet_fkQgt4CriticalFreeSphereConnectionEvent j)

theorem fkQgt4SiteRadius_sub_axisSite
    (j : Nat) (z : Site 2) :
    fkQgt4SiteRadius (z - axisSite j) = l1dist 2 (axisSite j) z := by
  simp only [fkQgt4SiteRadius, l1dist, Fin.sum_univ_two,
    Pi.sub_apply]
  congr 1 <;>
    rw [show z _ - axisSite j _ = -(axisSite j _ - z _) by ring,
      Int.natAbs_neg]

theorem mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected
    (omega : ConfigSpace (Sym2 (Site 2))) (j : Nat) {z : Site 2}
    (hconn : Connected 2 omega (axisSite j) z)
    (hdist : l1dist 2 (axisSite j) z = j) :
    omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent j := by
  let g := axisToOriginShift j
  have hga : g • axisSite j = origin 2 := by
    change -axisSite j + axisSite j = origin 2
    rw [neg_add_cancel]
    funext i
    fin_cases i <;> rfl
  have hgz : g • z = z - axisSite j := by
    change -axisSite j + z = z - axisSite j
    abel
  have hzSphere : g • z ∈ fkQgt4SiteSphere j := by
    rw [hgz]
    simp only [fkQgt4SiteSphere, Set.Finite.mem_toFinset,
      Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · intro i
      calc
        ((z - axisSite j) i).natAbs ≤
            fkQgt4SiteRadius (z - axisSite j) := by
          unfold fkQgt4SiteRadius
          fin_cases i
          · exact Nat.le_add_right _ _
          · exact Nat.le_add_left _ _
        _ = j := by rw [fkQgt4SiteRadius_sub_axisSite, hdist]
    · rw [fkQgt4SiteRadius_sub_axisSite, hdist]
  change ConfigSpace.shift g omega ∈
    fkQgt4CriticalFreeSphereConnectionEvent j
  unfold fkQgt4CriticalFreeSphereConnectionEvent
  rw [Set.mem_iUnion]
  refine ⟨g • z, ?_⟩
  rw [Set.mem_iUnion]
  refine ⟨hzSphere, ?_⟩
  change Connected 2 (ConfigSpace.shift g omega) (origin 2) (g • z)
  rw [← hga]
  exact (connected_shift g omega (axisSite j) z).2 hconn


theorem squareBoxClusterUnion_open_closed
    (eta : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    {x y : Site 2} (hx : x ∈ squareBoxClusterUnion eta n)
    (hxy : (openSubgraph 2 eta).Adj x y) :
    y ∈ squareBoxClusterUnion eta n := by
  obtain ⟨a, ha, hax⟩ :=
    (mem_squareBoxClusterUnion_iff eta n x).1 hx
  exact (mem_squareBoxClusterUnion_iff eta n y).2
    ⟨a, ha, hax.trans hxy.reachable⟩


theorem squareHoleFill_open_closed
    (eta : ConfigSpace (Sym2 (Site 2)))
    (S : Set (Site 2)) (hS : S.Finite)
    (hclosed : ∀ {x y}, x ∈ S → (openSubgraph 2 eta).Adj x y → y ∈ S)
    {x y : Site 2} (hx : x ∈ squareHoleFill S hS)
    (hxy : (openSubgraph 2 eta).Adj x y) :
    y ∈ squareHoleFill S hS := by
  by_cases hxS : x ∈ S
  · exact subset_squareHoleFill S hS (hclosed hxS hxy)
  by_cases hyS : y ∈ S
  · have hxS' := hclosed hyS hxy.symm
    exact (hxS hxS').elim
  intro hyOut
  have hyReach : (latticeMinusBarrier S).Reachable
      (beacon 2 (squareHoleFillRadius S hS)) y := by
    simpa [squareHoleFill, squareOuterComponent] using hyOut
  have hbar : (latticeMinusBarrier S).Adj y x :=
    latticeMinusBarrier_adj_of_both_not_mem S hxy.1.symm hyS hxS
  exact hx (hyReach.trans hbar.reachable)

theorem barrier_reachable_to_lattice_induce
    (A : Set (Site 2)) {x y : Site 2} (hx : x ∈ A) (hy : y ∈ A)
    (hxy : (latticeMinusBarrier A).Reachable x y) :
    ((hypercubicLattice 2).induce A).Reachable ⟨x, hx⟩ ⟨y, hy⟩ := by
  obtain ⟨w⟩ := hxy
  let wl : (hypercubicLattice 2).Walk x y :=
    w.map (Hom.ofLE (latticeMinusBarrier_le A))
  have hw : ∀ z ∈ wl.support, z ∈ A := by
    intro z hz
    change z ∈ (w.map (Hom.ofLE (latticeMinusBarrier_le A))).support at hz
    rw [Walk.support_map] at hz
    have hz' : z ∈ w.support := by simpa using hz
    exact (latticeMinusBarrier_sameSide A (w.takeUntil z hz')).mp hx
  exact walk_induce_reachable _ A wl hw hx hy


theorem squareHoleFill_inverseDual_faceBoundaryGraph_le
    (omega : ConfigSpace (Sym2 (Site 2)))
    (S : Set (Site 2)) (hS : S.Finite)
    (hclosed : ∀ {x y}, x ∈ S →
      (openSubgraph 2 (inverseFaceDualConfig omega)).Adj x y → y ∈ S) :
    faceBoundaryGraph (squareHoleFill S hS) ≤ openSubgraph 2 omega := by
  let K := squareHoleFill S hS
  have hKclosed : ∀ {x y}, x ∈ K →
      (openSubgraph 2 (inverseFaceDualConfig omega)).Adj x y → y ∈ K :=
    by
      intro x y hx hxy
      exact squareHoleFill_open_closed
        (inverseFaceDualConfig omega) S hS hclosed hx hxy
  intro f g hfg
  rcases hfg with ⟨hlat, hbd⟩
  refine ⟨hlat, ?_⟩
  by_contra hopen
  have homega : omega s(f, g) = false := Bool.eq_false_of_not_eq_true hopen
  obtain ⟨p, q, hpq, hpqAdj⟩ := sharedPrimalEdge_isLatticeEdge hlat
  have hinv : fci_faceEdgeEquiv.symm s(p, q) = s(f, g) := by
    apply fci_faceEdgeEquiv.injective
    rw [fci_faceEdgeEquiv.apply_symm_apply, ← hpq]
    exact (fci_faceEdgeEquiv_mk_of_adj hlat).symm
  have hetaOpen : (openSubgraph 2 (inverseFaceDualConfig omega)).Adj p q := by
    refine ⟨hpqAdj, ?_⟩
    simp [inverseFaceDualConfig, hinv, homega]
  rw [hpq, bdEdge_mk] at hbd
  by_cases hpK : p ∈ K
  · exact (hbd.mp hpK) (hKclosed hpK hetaOpen)
  · have hqK : q ∈ K := by
      by_contra hqK
      exact hpK (hbd.mpr hqK)
    exact hpK (hKclosed hqK hetaOpen.symm)


theorem exists_axisAnchoredSphereConnection_of_inverseDual_clusters_finite
    (omega : ConfigSpace (Sym2 (Site 2))) (n : Nat)
    (hfinite : ∀ x : Site 2,
      (cluster 2 (inverseFaceDualConfig omega) x).Finite) :
    ∃ j ≥ n, omega ∈ fkQgt4AxisAnchoredSphereConnectionEvent j := by
  let eta := inverseFaceDualConfig omega
  let S := squareBoxClusterUnion eta n
  let hS : S.Finite := squareBoxClusterUnion_finite eta n
    (fun x _ => hfinite x)
  let K := squareHoleFill S hS
  let hK : K.Finite := squareHoleFill_finite S hS
  have hzeroBox : origin 2 ∈ box 2 n := by
    intro i
    fin_cases i <;> simp [origin]
  have hzeroS : origin 2 ∈ S :=
    box_subset_squareBoxClusterUnion eta n hzeroBox
  have hzeroK : origin 2 ∈ K := subset_squareHoleFill S hS hzeroS
  have hKconn : ∀ a b : K,
      ((hypercubicLattice 2).induce K).Reachable a b := by
    intro a b
    apply barrier_reachable_to_lattice_induce K a.2 b.2
    exact squareHoleFill_inside_connected S hS ⟨origin 2, hzeroS⟩
      (squareBoxClusterUnion_connected eta n) a b a.2 b.2
  let rho := squareRegionConfig K
  have hrhoCluster : cluster 2 rho (origin 2) = K := by
    exact squareRegionConfig_cluster_eq K hzeroK hKconn
  have hrhoFinite : (cluster 2 rho (origin 2)).Finite := by
    rw [hrhoCluster]
    exact hK
  let j := exitIndex (ω := rho) hrhoFinite
  have hjge : n ≤ j := by
    by_contra hnot
    have hjlt : j < n := Nat.lt_of_not_ge hnot
    have haxisBox : axisSite (j + 1) ∈ box 2 n := by
      intro i
      fin_cases i <;> simp [axisSite] <;> omega
    have haxisS : axisSite (j + 1) ∈ S :=
      box_subset_squareBoxClusterUnion eta n haxisBox
    have haxisK : axisSite (j + 1) ∈ K :=
      subset_squareHoleFill S hS haxisS
    have hout := axisSite_exit_succ_not_mem (ω := rho) hrhoFinite
    rw [hrhoCluster] at hout
    exact hout haxisK
  have hface : FaceBoundaryConnected K (phb_boundarySupport K hK) := by
    simpa [eta, S, hS, K, hK] using
      squareBoxClusterUnion_fill_boundary_connected eta n
        (fun x _ => hfinite x)
  have hright : (faceBoundaryGraph K).Adj
      (exitFaceUp (ω := rho) hrhoFinite)
      (exitFaceDown (ω := rho) hrhoFinite) := by
    have h := exitFaces_faceBoundaryGraph_adj (ω := rho) hrhoFinite
    rwa [hrhoCluster] at h
  have hleft : (faceBoundaryGraph K).Adj
      (leftExitFaceUp (ω := rho) hrhoFinite)
      (leftExitFaceDown (ω := rho) hrhoFinite) := by
    have h := leftExitFaces_faceBoundaryGraph_adj (ω := rho) hrhoFinite
    rwa [hrhoCluster] at h
  have hrT : exitFaceUp (ω := rho) hrhoFinite ∈
      (phb_boundarySupport K hK : Set (Site 2)) := by
    simpa using hright.mem_support_left
  have hlT : leftExitFaceUp (ω := rho) hrhoFinite ∈
      (phb_boundarySupport K hK : Set (Site 2)) := by
    simpa using hleft.mem_support_left
  rw [FaceBoundaryConnected] at hface
  obtain ⟨w⟩ := hface.preconnected
    ⟨exitFaceUp (ω := rho) hrhoFinite, hrT⟩
    ⟨leftExitFaceUp (ω := rho) hrhoFinite, hlT⟩
  let incl : (faceBoundaryGraph K).induce
      (phb_boundarySupport K hK : Set (Site 2)) →g faceBoundaryGraph K :=
    { toFun := Subtype.val
      map_rel' := fun {a b} hab => hab }
  let wb := w.map incl
  have hboundaryOpen : faceBoundaryGraph K ≤ openSubgraph 2 omega := by
    apply squareHoleFill_inverseDual_faceBoundaryGraph_le omega S hS
    intro x y hx hxy
    exact squareBoxClusterUnion_open_closed eta n hx hxy
  let wo := wb.map (Hom.ofLE hboundaryOpen)
  let wl := wo.map (Hom.ofLE (openSubgraph_le omega))
  have hfar : j ≤ l1dist 2
      (exitFaceUp (ω := rho) hrhoFinite)
      (leftExitFaceUp (ω := rho) hrhoFinite) := by
    exact exitIndex_le_l1dist_of_leftFace (ω := rho) hrhoFinite
      (leftExitFaceUp_coord0_nonpos (ω := rho) hrhoFinite)
  have hwlStart : l1dist 2
      (exitFaceUp (ω := rho) hrhoFinite)
      (exitFaceUp (ω := rho) hrhoFinite) ≤ j := by simp
  have hwlEnd : j ≤ l1dist 2
      (exitFaceUp (ω := rho) hrhoFinite)
      (leftExitFaceUp (ω := rho) hrhoFinite) := hfar
  obtain ⟨z, hz, hdist⟩ := latticeWalk_hits_l1Sphere
    (exitFaceUp (ω := rho) hrhoFinite) wl j hwlStart hwlEnd
  have hzOpen : z ∈ wo.support := by
    change z ∈ (wo.map (Hom.ofLE (openSubgraph_le omega))).support at hz
    rw [Walk.support_map] at hz
    simpa using hz
  have hconn : Connected 2 omega
      (exitFaceUp (ω := rho) hrhoFinite) z :=
    ⟨wo.takeUntil z hzOpen⟩
  have hexit : exitFaceUp (ω := rho) hrhoFinite = axisSite j := by
    funext i
    fin_cases i <;> rfl
  refine ⟨j, hjge, ?_⟩
  apply mem_fkQgt4AxisAnchoredSphereConnectionEvent_of_connected omega j
  · simpa [hexit] using hconn
  · simpa [hexit] using hdist


end
end StatMech.FrontierD
