/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/HexagonalSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.HexagonalSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.HexagonalTranslatedArm.Part4
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part3
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalBoxToBufferedAt_injective (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    Function.Injective (hexagonalBoxToBufferedAt k m hkm) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : hexagonal.BufferedVertex m => (z : HexVertex)) h

theorem hexagonalBoxToBufferedAt_adjMatch (k m : Nat)
    (hkm : 2 * k ≤ hexagonal.bufferedRadius m) :
    ocd_AdjMatch (hexagonalBoxGraph (2 * k))
      (hexagonal.bufferedGraph m) (hexagonalBoxToBufferedAt k m hkm) := by
  intro x y
  rfl

theorem hexagonalBoxToBufferedAt_not_boundary
    (k m : Nat) (hkm : 2 * k < m)
    (x : HexagonalBoxVertex (2 * k)) :
    ¬ hexagonal.bufferedBoundary m
      (hexagonalBoxToBufferedAt k m
        ((hexagonal.id_le_bufferedRadius (2 * k)).trans
          (hexagonal.bufferedRadius_strictMono.monotone hkm.le)) x) := by
  intro hx
  have hxEarlier : x.1 ∈
      hexagonal.orbitBox (hexagonal.bufferedRadius (2 * k)) := by
    rw [hexagonal_mem_orbitBox_iff_box]
    exact box_mono 2 (hexagonal.id_le_bufferedRadius (2 * k)) x.2.1
  exact (hexagonal.bufferedBoundary_not_mem_of_lt hkm _ hx) hxEarlier

theorem hexagonalBoxToBufferedAt_boundary_of_adj_outside
    (k : Nat) (hk : 1 ≤ k)
    (x : HexagonalBoxVertex (2 * k))
    (z : HexVertex) (hxz : hexagonalGraph.Adj x.1 z)
    (hz : z.1 ∉ box 2 (2 * k)) :
    x ∈ hexagonalBoxShell (2 * k) (2 * k) := by
  have hxtrans : x.1.1 ∈ hexagonalTransBox (2 * k) (0 : Site 2) := by
    simpa only [hexagonalTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using x.2.1
  have hztrans : z.1 ∉ hexagonalTransBox (2 * k) (0 : Site 2) := by
    simpa only [hexagonalTransBox, StatMech.FK.fvs_transBox,
      Set.mem_setOf_eq, sub_zero] using hz
  have hboundary := hexagonalTransBox_boundary_of_adj_outside
    (x := (0 : Site 2)) (R := 2 * k) (by omega)
    ⟨x.1, ⟨hxtrans, Set.mem_univ _⟩⟩ z hxz hztrans
  simp [hexagonalBoxShell, hexagonalTransBoxBoundary,
    vertexBoundary] at hboundary ⊢
  exact hboundary

theorem hexagonalBoxToBufferedAt_inducedWiring_le
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (psi : ConfigSpace (Sym2 (hexagonal.BufferedVertex m))) :
    ocd_inducedWiring (hexagonal.bufferedGraph m)
        (hexagonalBoxToBufferedAt k m
          ((hexagonal.id_le_bufferedRadius (2 * k)).trans
            (hexagonal.bufferedRadius_strictMono.monotone hkm.le)))
        (hexagonal.bufferedBoundary m) psi ≤
      boundaryCliqueGraph
        (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k)) := by
  let hrad : 2 * k ≤ hexagonal.bufferedRadius m :=
    (hexagonal.id_le_bufferedRadius (2 * k)).trans
      (hexagonal.bufferedRadius_strictMono.monotone hkm.le)
  let incl := hexagonalBoxToBufferedAt k m hrad
  apply StatMech.FK.ocd_comapInducedWiring_le hexagonalGraph incl
    (fun _ => rfl) (hexagonalBoxToBufferedAt_injective k m hrad)
    (hexagonal.bufferedBoundary m)
    (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k))
  · intro x
    exact hexagonalBoxToBufferedAt_not_boundary k m hkm x
  · intro x z hxz hz
    apply hexagonalBoxToBufferedAt_boundary_of_adj_outside k hk x z hxz
    intro hzbox
    exact hz ⟨hzbox, Set.mem_univ _⟩

theorem hexagonalBufferedInnerShell_finite_le_theta
    (k m : Nat) (hk : 1 ≤ k) (hkm : 2 * k < m)
    (q beta : Real) (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedMeasure m
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (2 * k)
          (hexagonalBufferedInnerShellEvent k)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have hNm : 2 * k ≤ m := hkm.le
  let hrad : 2 * k ≤ hexagonal.bufferedRadius m :=
    (hexagonal.id_le_bufferedRadius (2 * k)).trans
      (hexagonal.bufferedRadius_strictMono.monotone hNm)
  let incl := hexagonalBoxToBufferedAt k m hrad
  have hcomp : ∀ omega : ConfigSpace (Sym2 (hexagonal.BufferedVertex m)),
      ocd_innerRestrict (hexagonalBoxToBuffered k)
          (hexagonal.bufferedRestrictLE hNm omega) =
        ocd_innerRestrict incl omega := by
    intro omega
    funext e
    have hv : ∀ x : HexagonalBoxVertex (2 * k),
        hexagonal.bufferedVertexInclLE hNm (hexagonalBoxToBuffered k x) =
          incl x := by
      intro x
      apply Subtype.ext
      rfl
    induction e using Sym2.inductionOn with
    | _ x y =>
        change omega s(hexagonal.bufferedVertexInclLE hNm
            (hexagonalBoxToBuffered k x),
          hexagonal.bufferedVertexInclLE hNm
            (hexagonalBoxToBuffered k y)) =
          omega s(incl x, incl y)
        rw [hv x, hv y]
  have hdom := ocd_wired_inner_dominated_bcProb
    (Gin := hexagonalBoxGraph (2 * k))
    (Gout := hexagonal.bufferedGraph m)
    (ιV := incl)
    (bdryOut := hexagonal.bufferedBoundary m)
    (hexagonalBoxToBufferedAt_injective k m hrad)
    (hexagonalBoxToBufferedAt_adjMatch k m hrad)
    (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k))
    hp hp1 hq
    (hexagonalBoxToBufferedAt_inducedWiring_le k m hk hkm)
    (hexagonalCenteredShellFullEvent_increasing (2 * k) k)
  rw [hexagonal.wiredBufferedMeasure_real_cylinder hNm hp hp1
    (zero_lt_one.trans_le hq) (hexagonalBufferedInnerShellEvent k)]
  have heventEq :
      hexagonal.bufferedRestrictLE hNm ⁻¹'
          hexagonalBufferedInnerShellEvent k =
        ocd_innerRestrict incl ⁻¹'
          hexagonalCenteredShellFullEvent (2 * k) k := by
    ext omega
    simp only [Set.mem_preimage, hexagonalBufferedInnerShellEvent, hcomp]
  rw [heventEq]
  calc
    (∑ omega,
        (ocd_innerRestrict incl ⁻¹'
          hexagonalCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonal.bufferedGraph m)
            (hexagonal.bufferedBoundary m) p q omega) ≤
      ∑ omega,
        (hexagonalCenteredShellFullEvent (2 * k) k).indicator
            (fun _ => (1 : Real)) omega *
          wiredFkProb (hexagonalBoxGraph (2 * k))
            (fun x => x ∈ hexagonalBoxShell (2 * k) (2 * k)) p q omega := by
        simpa only [bcProb_clique_eq_wiredFkProb] using hdom
    _ = hexagonalOuterInnerTheta q beta k := by
      simpa [p] using hexagonalCenteredFullMass_eq_outerInnerTheta
        k hk q beta hq hbeta

theorem hexagonalBufferedInnerShell_infinite_le_theta
    (k : Nat) (hk : 1 ≤ k) (q beta : Real)
    (hq : 1 ≤ q) (hbeta : 0 < beta) :
    (hexagonal.wiredBufferedInfiniteVolume
        (by
          rw [sub_pos]
          exact Real.exp_lt_one_iff.mpr (by linarith))
        (by linarith [Real.exp_pos (-beta)] : 1 - Real.exp (-beta) < 1)
        (zero_lt_one.trans_le hq) : Measure (ConfigSpace (Sym2 HexVertex))).real
        (hexagonal.bufferedCylinder (2 * k)
          (hexagonalBufferedInnerShellEvent k)) ≤
      hexagonalOuterInnerTheta q beta k := by
  let p := 1 - Real.exp (-beta)
  have hp : 0 < p := by
    unfold p
    rw [sub_pos]
    exact Real.exp_lt_one_iff.mpr (by linarith)
  have hp1 : p < 1 := by unfold p; linarith [Real.exp_pos (-beta)]
  have htend := hexagonal.wiredBufferedMeasure_tendsto_cylinder
    (2 * k) hp hp1 hq (hexagonalBufferedInnerShellEvent_increasing k)
  apply le_of_tendsto htend
  filter_upwards [Filter.eventually_ge_atTop (2 * k + 1)] with m hm
  exact hexagonalBufferedInnerShell_finite_le_theta
    k m hk (by omega) q beta hq hbeta

theorem hexagonal_root_coord_eq_zero : hexagonal.root.1 = (0 : Site 2) := by
  have h : hexagonal.root = ((0, false) : HexVertex) ∨
      hexagonal.root = ((0, true) : HexVertex) := by
    simpa [hexagonal] using hexagonal.root_mem_fundamentalDomain
  rcases h with h | h <;> simp [h]

theorem site_neg_mem_box {n : Nat} {x : Site 2} (hx : x ∈ box 2 n) :
    -x ∈ box 2 n := by
  intro i
  simpa using hx i


end StatMech.FK.PeriodicPlanar
