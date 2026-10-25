/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpness.Part5
import Theorem.StatisticalMechanics.Code.FK.BoundaryEdgeAbsorption.Part3
import Theorem.StatisticalMechanics.Code.OSSS.FKSharpnessWeightedDomainActive
import Def.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem restrictActive_preimage_triangularCenteredShellEvent
    (R k : Nat) :
    restrictActive (triangularBoxGraph R) ⁻¹'
        triangularCenteredShellEvent R k =
      triangularCenteredShellFullEvent R k := by
  ext omega
  change ConnOpenSet (triangularBoxEndU R) (triangularBoxEndV R)
      (restrictActive (triangularBoxGraph R) omega)
      (triangularBoxRoot R) (triangularBoxShell R k) ↔
    ∃ y ∈ triangularBoxShell R k,
      (openSub (triangularBoxGraph R) omega).Reachable (triangularBoxRoot R) y
  unfold triangularBoxEndU triangularBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp

theorem restrictActive_preimage_triangularTransShellEvent
    (R k : Nat) (x : Site 2) :
    restrictActive (triangularTransBoxGraph R x) ⁻¹'
        triangularTransShellEvent R k x =
      triangularTransShellFullEvent R k x := by
  ext omega
  change ConnOpenSet (triangularTransBoxEndU R x)
      (triangularTransBoxEndV R x)
      (restrictActive (triangularTransBoxGraph R x) omega)
      (triangularTransBoxCenter R x) (triangularTransBoxShell R k x) ↔
    ∃ y ∈ triangularTransBoxShell R k x,
      (openSub (triangularTransBoxGraph R x) omega).Reachable
        (triangularTransBoxCenter R x) y
  unfold triangularTransBoxEndU triangularTransBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp


theorem reCfgIso_preimage_triangularCenteredShellFullEvent
    (R k : Nat) (x : Site 2) :
    reCfgIso (StatMech.FK.fvs_transEquiv 2 R x) ⁻¹'
        triangularCenteredShellFullEvent R k =
      triangularTransShellFullEvent R k x := by
  ext omega
  let sigma := StatMech.FK.fvs_transEquiv 2 R x
  let iso := fvs_openSubIso (triangularBoxGraph R)
    (triangularTransBoxGraph R x) sigma
    (triangularTransEquiv_adj R x) omega
  constructor
  · rintro ⟨y, hy, hreach⟩
    refine ⟨sigma y, (triangularTransEquiv_mem_shell R k x y).2 hy, ?_⟩
    rw [← triangularTransEquiv_center R x]
    exact iso.reachable_iff.mpr hreach
  · rintro ⟨y, hy, hreach⟩
    let y0 : TriangularBoxVertex R := sigma.symm y
    refine ⟨y0, ?_, ?_⟩
    · apply (triangularTransEquiv_mem_shell R k x y0).1
      simpa [sigma, y0] using hy
    · apply iso.reachable_iff.mp
      change (openSub (triangularTransBoxGraph R x) omega).Reachable
        (sigma (triangularBoxRoot R)) (sigma y0)
      rw [triangularTransEquiv_center]
      simpa [sigma, y0] using hreach


theorem triangularTransEquiv_boundary (R : Nat) (x : Site 2)
    (y : TriangularBoxVertex R) :
    y ∈ triangularBoxShell R R ↔
      triangularTransBoxBoundary R x
        (StatMech.FK.fvs_transEquiv 2 R x y) := by
  simp [triangularBoxShell, triangularTransBoxBoundary,
    StatMech.FK.fvs_transEquiv_val]


theorem triangularTransShellEvent_activeBCMean_eq_centeredFullMass
    (R k : Nat) (x : Site 2) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    activeBCMean (triangularTransBoxGraph R x)
        (boundaryCliqueGraph (triangularTransBoxBoundary R x))
        (fun _ => p) q
        ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R) p q omega := by
  rw [activeBCMean_boundaryClique_eq_wired
    (triangularTransBoxGraph R x) (triangularTransBoxBoundary R x)
    hp hp1 hq]
  calc
    (∑ omega : ConfigSpace (Sym2 (TriangularTransBoxVertex R x)),
        (triangularTransShellEvent R k x).indicator (fun _ => (1 : Real))
            (restrictActive (triangularTransBoxGraph R x) omega) *
          wiredFkProb (triangularTransBoxGraph R x)
            (triangularTransBoxBoundary R x) p q omega) =
      ∑ omega : ConfigSpace (Sym2 (TriangularTransBoxVertex R x)),
        (triangularTransShellFullEvent R k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularTransBoxGraph R x)
            (triangularTransBoxBoundary R x) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      have hevent :
          restrictActive (triangularTransBoxGraph R x) omega ∈
              triangularTransShellEvent R k x ↔
            omega ∈ triangularTransShellFullEvent R k x := by
        rw [← Set.mem_preimage]
        exact Set.ext_iff.mp
          (restrictActive_preimage_triangularTransShellEvent R k x) omega
      by_cases h : restrictActive (triangularTransBoxGraph R x) omega ∈
          triangularTransShellEvent R k x
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hevent.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (mt hevent.mpr h)]
    _ = ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R) p q omega := by
      rw [← cdc_eventMassProb_reCfgIso_inv
        (StatMech.FK.fvs_transEquiv 2 R x)
        (wiredFkProb (triangularBoxGraph R)
          (fun y => y ∈ triangularBoxShell R R) p q)
        (wiredFkProb (triangularTransBoxGraph R x)
          (triangularTransBoxBoundary R x) p q)
        (fun omega => fvs_wiredFkProb_reCfgIso
          (triangularBoxGraph R) (triangularTransBoxGraph R x)
          (fun y => y ∈ triangularBoxShell R R)
          (triangularTransBoxBoundary R x)
          (StatMech.FK.fvs_transEquiv 2 R x)
          (triangularTransEquiv_adj R x)
          (triangularTransEquiv_boundary R x) p q omega)
        (triangularCenteredShellFullEvent R k)]
      rw [reCfgIso_preimage_triangularCenteredShellFullEvent]


theorem triangularTransShellEvent_betaMean_eq_centeredFullMass
    (R k : Nat) (x : Site 2) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    activeBCMean (triangularTransBoxGraph R x)
        (boundaryCliqueGraph (triangularTransBoxBoundary R x))
        (betaParams (fun _ => 1) beta) q
        ((triangularTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (TriangularBoxVertex R)),
        (triangularCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (triangularBoxGraph R)
            (fun y => y ∈ triangularBoxShell R R)
            (1 - Real.exp (-beta)) q omega := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have hparam : betaParams (fun _ : Sym2 (TriangularTransBoxVertex R x) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [betaParams]
  rw [hparam]
  exact triangularTransShellEvent_activeBCMean_eq_centeredFullMass
    R k x hp hp1 hq


theorem triangularTransBox_subset_double
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n) :
    triangularTransBox (2 * k) x ⊆ box 2 (2 * n) := by
  intro y hy i
  have hyi : ((y - x) i).natAbs <= 2 * k := hy i
  have hxi : (x i).natAbs <= n := hx i
  have heq : y i = (y i - x i) + x i := by ring
  calc
    (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← heq]
    _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
    _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
    _ <= 2 * k + n := Nat.add_le_add hyi hxi
    _ <= 2 * n := by omega


theorem triangularTransBox_outer_margin
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n)
    (y : TriangularTransBoxVertex (2 * k) x) :
    triangularTransBoxIncl (triangularTransBox_subset_double hx hkn) y ∉
      triangularBoxShell (2 * n) (2 * n) := by
  intro hybdry
  have hycoord := (Finset.mem_filter.mp hybdry).2.2
  have hybox : y.1 ∈ box 2 (2 * n - 1) := by
    intro i
    have hyi : ((y.1 - x) i).natAbs <= 2 * k := y.2 i
    have hxi : (x i).natAbs <= n := hx i
    have heq : y.1 i = (y.1 i - x i) + x i := by ring
    calc
      (y.1 i).natAbs = ((y.1 i - x i) + x i).natAbs := by rw [← heq]
      _ <= (y.1 i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y.1 - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n - 1 := by omega
  exact hycoord hybox

theorem triangular_adj_sub_right (x : Site 2) {y z : Site 2}
    (hyz : triangularGraph.Adj y z) :
    triangularGraph.Adj (y - x) (z - x) := by
  rw [triangularGraph_adj] at hyz ⊢
  obtain ⟨i, h | h⟩ := hyz
  · refine ⟨i, Or.inl ?_⟩
    calc
      (z - x) - (y - x) = z - y := by abel
      _ = triangularStep i := h
  · refine ⟨i, Or.inr ?_⟩
    calc
      (y - x) - (z - x) = y - z := by abel
      _ = triangularStep i := h


theorem triangularTransBox_boundary_of_adj_outside
    {R : Nat} (hR : 1 <= R) {x : Site 2}
    (y : TriangularTransBoxVertex R x) (z : Site 2)
    (hyz : triangularGraph.Adj y.1 z) (hz : z ∉ triangularTransBox R x) :
    triangularTransBoxBoundary R x y := by
  have hybox : y.1 - x ∈ box 2 R := y.2
  have hzstep : z - x ∈ box 2 (R + 1) := by
    have hadj : triangularGraph.Adj (y.1 - x) (z - x) :=
      triangular_adj_sub_right x hyz
    exact triangular_adj_mem_box_succ hybox hadj
  refine ⟨hybox, ?_⟩
  intro hsmall
  have hzR : z - x ∈ box 2 R := by
    have hadj : triangularGraph.Adj (y.1 - x) (z - x) :=
      triangular_adj_sub_right x hyz
    exact triangular_adj_mem_box_of_mem_pred hR hsmall hadj
  exact hz hzR


theorem triangularTransBox_inducedWiring_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * n)))) :
    ocd_inducedWiring (triangularBoxGraph (2 * n))
        (triangularTransBoxIncl (triangularTransBox_subset_double hx hkn))
        (fun y => y ∈ triangularBoxShell (2 * n) (2 * n)) psi <=
      boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x) := by
  let hsub := triangularTransBox_subset_double hx hkn
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph
    (triangularTransBoxIncl hsub)
    (fun _ => rfl) (triangularTransBoxIncl_injective hsub)
    (fun y => y ∈ triangularBoxShell (2 * n) (2 * n))
    (triangularTransBoxBoundary (2 * k) x)
  · intro y
    exact triangularTransBox_outer_margin hx hkn y
  · intro y z hyz hz
    exact triangularTransBox_boundary_of_adj_outside (by omega) y z hyz hz


theorem triangularTransBox_activeBCMean_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    {A : Set (ConfigSpace (triangularTransBoxGraph (2 * k) x).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (triangularBoxGraph (2 * n))
        (boundaryCliqueGraph
          (fun y => y ∈ triangularBoxShell (2 * n) (2 * n)))
        (betaParams (fun _ => 1) beta) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive
            (triangularTransBoxGraph (2 * k) x)
            (triangularBoxGraph (2 * n))
            (triangularTransBoxIncl
              (triangularTransBox_subset_double hx hkn))
            (ocd_comapAdjMatch triangularGraph
              (triangularTransBoxIncl
                (triangularTransBox_subset_double hx hkn))
              (fun _ => rfl)) rho)) <=
      activeBCMean (triangularTransBoxGraph (2 * k) x)
        (boundaryCliqueGraph (triangularTransBoxBoundary (2 * k) x))
        (betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
  let hsub := triangularTransBox_subset_double hx hkn
  let iota := triangularTransBoxIncl hsub
  have hadjm : ocd_AdjMatch (triangularTransBoxGraph (2 * k) x)
      (triangularBoxGraph (2 * n)) iota :=
    ocd_comapAdjMatch triangularGraph iota (fun _ => rfl)
  have hparam : ocd_ParamCompatible iota
      (betaParams (fun _ => 1) beta)
      (betaParams (fun _ => 1) beta) := by
    intro e
    simp [betaParams]
  have hwire := fun psi => triangularTransBox_inducedWiring_le
    hx hk hkn psi
  exact ocd_wired_inner_dominated_activeBCMean
    (triangularTransBoxGraph (2 * k) x) (triangularBoxGraph (2 * n)) iota
    (fun y => y ∈ triangularBoxShell (2 * n) (2 * n))
    (triangularTransBoxIncl_injective hsub) hadjm
    (triangularTransBoxBoundary (2 * k) x) hparam
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta)
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta) hq hwire hA

end
end StatMech.FK.PeriodicPlanar
