/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalOffCentre.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularOffCentre.Part5
import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpness.Part5
import Def.StatisticalMechanics.Code.FK.HexagonalOffCentre.Part7
open scoped BigOperators Classical
open Finset Set SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS.RevealmentConstruction

open StatMech.OSSS.FiniteGraphBoundaryDifferential

noncomputable section

theorem restrictActive_preimage_hexagonalCenteredShellEvent
    (R k : Nat) :
    restrictActive (hexagonalBoxGraph R) ⁻¹'
        hexagonalCenteredShellEvent R k =
      hexagonalCenteredShellFullEvent R k := by
  ext omega
  change ConnOpenSet (hexagonalBoxEndU R) (hexagonalBoxEndV R)
      (restrictActive (hexagonalBoxGraph R) omega)
      (hexagonalBoxRoot R) (hexagonalBoxShell R k) ↔
    ∃ y ∈ hexagonalBoxShell R k,
      (openSub (hexagonalBoxGraph R) omega).Reachable (hexagonalBoxRoot R) y
  unfold hexagonalBoxEndU hexagonalBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp

theorem restrictActive_preimage_hexagonalTransShellEvent
    (R k : Nat) (x : HexVertex) :
    restrictActive (hexagonalTransBoxGraph R x.1) ⁻¹'
        hexagonalTransShellEvent R k x =
      hexagonalTransShellFullEvent R k x := by
  ext omega
  change ConnOpenSet (hexagonalTransBoxEndU R x.1)
      (hexagonalTransBoxEndV R x.1)
      (restrictActive (hexagonalTransBoxGraph R x.1) omega)
      (hexagonalTransBoxCenter R x) (hexagonalTransBoxShell R k x.1) ↔
    ∃ y ∈ hexagonalTransBoxShell R k x.1,
      (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
        (hexagonalTransBoxCenter R x) y
  unfold hexagonalTransBoxEndU hexagonalTransBoxEndV
  rw [connOpenSet_edgeSet_iff_openSub]
  rw [openSub_extendActive_restrictActive_eq]
  simp


theorem reCfgIso_preimage_hexagonalCenteredShellFullEvent
    (R k : Nat) (x : HexVertex) :
    reCfgIso (hexagonalTransEquiv R x) ⁻¹'
        hexagonalCenteredShellFullEvent R k =
      hexagonalTransShellFullEvent R k x := by
  ext omega
  let sigma := hexagonalTransEquiv R x
  let iso := fvs_openSubIso (hexagonalBoxGraph R)
    (hexagonalTransBoxGraph R x.1) sigma
    (hexagonalTransEquiv_adj R x) omega
  constructor
  · rintro ⟨y, hy, hreach⟩
    refine ⟨sigma y, (hexagonalTransEquiv_mem_shell R k x y).2 hy, ?_⟩
    rw [← hexagonalTransEquiv_center R x]
    exact iso.reachable_iff.mpr hreach
  · rintro ⟨y, hy, hreach⟩
    let y0 : HexagonalBoxVertex R := sigma.symm y
    refine ⟨y0, ?_, ?_⟩
    · apply (hexagonalTransEquiv_mem_shell R k x y0).1
      simpa [sigma, y0] using hy
    · apply iso.reachable_iff.mp
      change (openSub (hexagonalTransBoxGraph R x.1) omega).Reachable
        (sigma (hexagonalBoxRoot R)) (sigma y0)
      rw [hexagonalTransEquiv_center]
      simpa [sigma, y0] using hreach


theorem hexagonalTransEquiv_boundary (R : Nat) (x : HexVertex)
    (y : HexagonalBoxVertex R) :
    y ∈ hexagonalBoxShell R R ↔
      hexagonalTransBoxBoundary R x.1
        (hexagonalTransEquiv R x y) := by
  cases hx : x.2 <;>
    simp [hexagonalBoxShell, hexagonalTransBoxBoundary,
      hexagonalTransEquiv, hx, sub_eq_add_neg, Int.natAbs_neg]


theorem hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass
    (R k : Nat) (x : HexVertex) {p q : Real}
    (hp : 0 < p) (hp1 : p < 1) (hq : 0 < q) :
    activeBCMean (hexagonalTransBoxGraph R x.1)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1))
        (fun _ => p) q
        ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R) p q omega := by
  rw [activeBCMean_boundaryClique_eq_wired
    (hexagonalTransBoxGraph R x.1) (hexagonalTransBoxBoundary R x.1)
    hp hp1 hq]
  calc
    (∑ omega : ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1)),
        (hexagonalTransShellEvent R k x).indicator (fun _ => (1 : Real))
            (restrictActive (hexagonalTransBoxGraph R x.1) omega) *
          wiredFkProb (hexagonalTransBoxGraph R x.1)
            (hexagonalTransBoxBoundary R x.1) p q omega) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalTransBoxVertex R x.1)),
        (hexagonalTransShellFullEvent R k x).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalTransBoxGraph R x.1)
            (hexagonalTransBoxBoundary R x.1) p q omega := by
      apply Finset.sum_congr rfl
      intro omega _
      have hevent :
          restrictActive (hexagonalTransBoxGraph R x.1) omega ∈
              hexagonalTransShellEvent R k x ↔
            omega ∈ hexagonalTransShellFullEvent R k x := by
        rw [← Set.mem_preimage]
        exact Set.ext_iff.mp
          (restrictActive_preimage_hexagonalTransShellEvent R k x) omega
      by_cases h : restrictActive (hexagonalTransBoxGraph R x.1) omega ∈
          hexagonalTransShellEvent R k x
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (hevent.mp h)]
      · rw [Set.indicator_of_notMem h,
          Set.indicator_of_notMem (mt hevent.mpr h)]
    _ = ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R) p q omega := by
      rw [← cdc_eventMassProb_reCfgIso_inv
        (hexagonalTransEquiv R x)
        (wiredFkProb (hexagonalBoxGraph R)
          (fun y => y ∈ hexagonalBoxShell R R) p q)
        (wiredFkProb (hexagonalTransBoxGraph R x.1)
          (hexagonalTransBoxBoundary R x.1) p q)
        (fun omega => fvs_wiredFkProb_reCfgIso
          (hexagonalBoxGraph R) (hexagonalTransBoxGraph R x.1)
          (fun y => y ∈ hexagonalBoxShell R R)
          (hexagonalTransBoxBoundary R x.1)
          (hexagonalTransEquiv R x)
          (hexagonalTransEquiv_adj R x)
          (hexagonalTransEquiv_boundary R x) p q omega)
        (hexagonalCenteredShellFullEvent R k)]
      rw [reCfgIso_preimage_hexagonalCenteredShellFullEvent]


theorem hexagonalTransShellEvent_betaMean_eq_centeredFullMass
    (R k : Nat) (x : HexVertex) (q beta : Real)
    (hq : 0 < q) (hbeta : 0 < beta) :
    activeBCMean (hexagonalTransBoxGraph R x.1)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary R x.1))
        (betaParams (fun _ => 1) beta) q
        ((hexagonalTransShellEvent R k x).indicator fun _ => (1 : Real)) =
      ∑ omega : ConfigSpace (Sym2 (HexagonalBoxVertex R)),
        (hexagonalCenteredShellFullEvent R k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph R)
            (fun y => y ∈ hexagonalBoxShell R R)
            (1 - Real.exp (-beta)) q omega := by
  have hp : 0 < 1 - Real.exp (-beta) := by
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : 1 - Real.exp (-beta) < 1 := by
    linarith [Real.exp_pos (-beta)]
  have hparam : betaParams (fun _ : Sym2 (HexagonalTransBoxVertex R x.1) => 1) beta =
      fun _ => 1 - Real.exp (-beta) := by
    funext e
    simp [betaParams]
  rw [hparam]
  exact hexagonalTransShellEvent_activeBCMean_eq_centeredFullMass
    R k x hp hp1 hq


theorem hexagonalTransBox_subset_double
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n) :
    hexagonalTransBox (2 * k) x ⊆ box 2 (2 * n) := by
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


theorem hexagonalTransBox_outer_margin
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n) (hkn : 2 * k < n)
    (y : HexagonalTransBoxVertex (2 * k) x) :
    hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn) y ∉
      hexagonalBoxShell (2 * n) (2 * n) := by
  intro hybdry
  have hycoord := (Finset.mem_filter.mp hybdry).2.2
  have hybox : y.1.1 ∈ box 2 (2 * n - 1) := by
    intro i
    have hyi : ((y.1.1 - x) i).natAbs <= 2 * k := y.2.1 i
    have hxi : (x i).natAbs <= n := hx i
    have heq : y.1.1 i = (y.1.1 i - x i) + x i := by ring
    calc
      (y.1.1 i).natAbs = ((y.1.1 i - x i) + x i).natAbs := by rw [← heq]
      _ <= (y.1.1 i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _
      _ = ((y.1.1 - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply]
      _ <= 2 * k + n := Nat.add_le_add hyi hxi
      _ <= 2 * n - 1 := by omega
  exact hycoord hybox

theorem hexagonal_adj_sub_right (x : Site 2) {y z : HexVertex}
    (hyz : hexagonalGraph.Adj y z) :
    hexagonalGraph.Adj (y.1 - x, y.2) (z.1 - x, z.2) := by
  rw [hexagonalGraph_adj] at hyz ⊢
  rcases hyz with ⟨hy, hz, i, h⟩ | ⟨hz, hy, i, h⟩
  · refine Or.inl ⟨hy, hz, i, ?_⟩
    calc
      (z.1 - x) - (y.1 - x) = z.1 - y.1 := by abel
      _ = hexagonalStep i := h
  · refine Or.inr ⟨hz, hy, i, ?_⟩
    calc
      (y.1 - x) - (z.1 - x) = y.1 - z.1 := by abel
      _ = hexagonalStep i := h


theorem hexagonalTransBox_boundary_of_adj_outside
    {R : Nat} (hR : 1 <= R) {x : Site 2}
    (y : HexagonalTransBoxVertex R x) (z : HexVertex)
    (hyz : hexagonalGraph.Adj y.1 z) (hz : z.1 ∉ hexagonalTransBox R x) :
    hexagonalTransBoxBoundary R x y := by
  have hybox : y.1.1 - x ∈ box 2 R := y.2.1
  have hzstep : z.1 - x ∈ box 2 (R + 1) := by
    have hadj : hexagonalGraph.Adj (y.1.1 - x, y.1.2) (z.1 - x, z.2) :=
      hexagonal_adj_sub_right x hyz
    exact hexagonal_adj_mem_box_succ hybox hadj
  refine ⟨hybox, ?_⟩
  intro hsmall
  have hzR : z.1 - x ∈ box 2 R := by
    have hadj : hexagonalGraph.Adj (y.1.1 - x, y.1.2) (z.1 - x, z.2) :=
      hexagonal_adj_sub_right x hyz
    exact hexagonal_adj_mem_box_of_mem_pred hR hsmall hadj
  exact hz hzR


theorem hexagonalTransBox_inducedWiring_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * n)))) :
    ocd_inducedWiring (hexagonalBoxGraph (2 * n))
        (hexagonalTransBoxIncl (hexagonalTransBox_subset_double hx hkn))
        (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n)) psi <=
      boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x) := by
  let hsub := hexagonalTransBox_subset_double hx hkn
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph
    (hexagonalTransBoxIncl hsub)
    (fun _ => rfl) (hexagonalTransBoxIncl_injective hsub)
    (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n))
    (hexagonalTransBoxBoundary (2 * k) x)
  · intro y
    exact hexagonalTransBox_outer_margin hx hkn y
  · intro y z hyz hz
    apply hexagonalTransBox_boundary_of_adj_outside (by omega) y z hyz
    intro hzcoord
    exact hz ⟨hzcoord, Set.mem_univ _⟩


theorem hexagonalTransBox_activeBCMean_le
    {n k : Nat} {x : Site 2} (hx : x ∈ box 2 n)
    (hk : 1 <= k) (hkn : 2 * k < n)
    (q beta : Real) (hq : 1 <= q) (hbeta : 0 < beta)
    {A : Set (ConfigSpace (hexagonalTransBoxGraph (2 * k) x).edgeSet)}
    (hA : IsIncreasing A) :
    activeBCMean (hexagonalBoxGraph (2 * n))
        (boundaryCliqueGraph
          (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n)))
        (betaParams (fun _ => 1) beta) q
        (fun rho => A.indicator (fun _ => (1 : Real))
          (ocd_innerRestrictActive
            (hexagonalTransBoxGraph (2 * k) x)
            (hexagonalBoxGraph (2 * n))
            (hexagonalTransBoxIncl
              (hexagonalTransBox_subset_double hx hkn))
            (ocd_comapAdjMatch hexagonalGraph
              (hexagonalTransBoxIncl
                (hexagonalTransBox_subset_double hx hkn))
              (fun _ => rfl)) rho)) <=
      activeBCMean (hexagonalTransBoxGraph (2 * k) x)
        (boundaryCliqueGraph (hexagonalTransBoxBoundary (2 * k) x))
        (betaParams (fun _ => 1) beta) q
        (A.indicator fun _ => (1 : Real)) := by
  let hsub := hexagonalTransBox_subset_double hx hkn
  let iota := hexagonalTransBoxIncl hsub
  have hadjm : ocd_AdjMatch (hexagonalTransBoxGraph (2 * k) x)
      (hexagonalBoxGraph (2 * n)) iota :=
    ocd_comapAdjMatch hexagonalGraph iota (fun _ => rfl)
  have hparam : ocd_ParamCompatible iota
      (betaParams (fun _ => 1) beta)
      (betaParams (fun _ => 1) beta) := by
    intro e
    simp [betaParams]
  have hwire := fun psi => hexagonalTransBox_inducedWiring_le
    hx hk hkn psi
  exact ocd_wired_inner_dominated_activeBCMean
    (hexagonalTransBoxGraph (2 * k) x) (hexagonalBoxGraph (2 * n)) iota
    (fun y => y ∈ hexagonalBoxShell (2 * n) (2 * n))
    (hexagonalTransBoxIncl_injective hsub) hadjm
    (hexagonalTransBoxBoundary (2 * k) x) hparam
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta)
    (betaParams_pos (fun _ => by norm_num) hbeta)
    (betaParams_lt_one (fun _ => 1) beta) hq hwire hA

end
end StatMech.FK.PeriodicPlanar
