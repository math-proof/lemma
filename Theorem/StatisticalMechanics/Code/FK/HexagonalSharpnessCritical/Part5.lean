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
import Def.StatisticalMechanics.Code.FK.HexagonalSharpnessCritical.Part5
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem hexagonalBufferedToBox_injective (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    Function.Injective (hexagonalBufferedToBox j N hjn) := by
  intro x y h
  apply Subtype.ext
  apply hexagonalRootFrame.injective
  exact congrArg (fun z : HexagonalBoxVertex (2 * N) => (z : HexVertex)) h

theorem hexagonalBufferedToBox_adjMatch (j N : Nat)
    (hjn : hexagonal.bufferedRadius j ≤ 2 * N) :
    ocd_AdjMatch (hexagonal.bufferedGraph j)
      (hexagonalBoxGraph (2 * N)) (hexagonalBufferedToBox j N hjn) := by
  intro x y
  exact (hexagonalRootFrame_adj x.1 y.1).symm

theorem hexagonalBufferedToBox_not_outerBoundary
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (x : hexagonal.BufferedVertex j) :
    hexagonalBufferedToBox j N (by omega) x ∉
      hexagonalBoxShell (2 * N) (2 * N) := by
  intro hx
  have hxSmall : (hexagonalRootFrame x.1).1 ∈ box 2 (2 * N - 1) := by
    rw [hexagonalRootFrame_coord_mem_box_iff]
    rw [← hexagonal_mem_orbitBox_iff_box]
    exact hexagonal.orbitBox_mono (by omega) x.2
  exact (Finset.mem_filter.mp hx).2.2 hxSmall

theorem hexagonalBufferedToBox_inducedWiring_le
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N)
    (psi : ConfigSpace (Sym2 (HexagonalBoxVertex (2 * N)))) :
    ocd_inducedWiring (hexagonalBoxGraph (2 * N))
        (hexagonalBufferedToBox j N (by omega))
        (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N)) psi ≤
      boundaryCliqueGraph (hexagonal.bufferedBoundary j) := by
  let incl := hexagonalBufferedToBox j N (by omega :
    hexagonal.bufferedRadius j ≤ 2 * N)
  apply StatMech.FK.ocd_comapInducedWiring_le_equiv hexagonalGraph
    hexagonalRootFrame hexagonalRootFrame_adj incl
    (fun _ => rfl) (hexagonalBufferedToBox_injective j N (by omega))
    (fun y => y ∈ hexagonalBoxShell (2 * N) (2 * N))
    (hexagonal.bufferedBoundary j)
  · intro x
    exact hexagonalBufferedToBox_not_outerBoundary j N hjn x
  · intro x z hxz hz
    exact ⟨z, hxz, by
      intro hzOrbit
      exact hz hzOrbit⟩

theorem hexagonalCenteredShellFullEvent_subset_bufferedRestrict
    (j N : Nat) (hjn : hexagonal.bufferedRadius j < N) :
    hexagonalCenteredShellFullEvent (2 * N) N ⊆
      ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) ⁻¹'
        hexagonal.bufferedRootBoundaryEvent j := by
  intro omega hcross
  obtain ⟨v, hvShell, hreach⟩ := hcross
  let S : Set (HexagonalBoxVertex (2 * N)) :=
    {x | x.1 ∈ hexagonal.orbitBox (hexagonal.bufferedRadius j)}
  have hrootS : hexagonalBoxRoot (2 * N) ∈ S := by
    change ((0, false) : HexVertex) ∈
      hexagonal.orbitBox (hexagonal.bufferedRadius j)
    rw [hexagonal_mem_orbitBox_iff_box]
    simp
  have hvOutside : v ∉ S := by
    intro hvS
    have hvSmall : v.1.1 ∈ box 2 (N - 1) := by
      rw [← hexagonal_mem_orbitBox_iff_box]
      exact hexagonal.orbitBox_mono (by omega) hvS
    exact (Finset.mem_filter.mp hvShell).2.2 hvSmall
  obtain ⟨y, hyReach, z, hyz, hzOutside⟩ :=
    reachable_induce_innerBoundary
      (FK.openSub (hexagonalBoxGraph (2 * N)) omega) S
      hrootS hvOutside hreach
  let phi : ((FK.openSub (hexagonalBoxGraph (2 * N)) omega).induce S) →g
      FK.openSub (hexagonal.bufferedGraph j)
        (ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) omega) := {
    toFun := fun x => (⟨hexagonalRootFrame.symm x.1.1, by
      change hexagonalRootFrame x.1.1 ∈
        hexagonal.orbitBox (hexagonal.bufferedRadius j)
      exact (hexagonalRootFrame_mem_orbitBox_iff _ _).2 x.2⟩ :
        hexagonal.BufferedVertex j)
    map_rel' := by
      intro a b hab
      change hexagonalGraph.Adj a.1.1 b.1.1 ∧
        omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨?_, ?_⟩
      · change hexagonalGraph.Adj (hexagonalRootFrame a.1.1)
          (hexagonalRootFrame b.1.1)
        exact (hexagonalRootFrame_adj _ _).2 hab.1
      simpa [ocd_innerRestrict, ocd_innerEdge, hexagonalBufferedToBox]
        using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨hexagonalBoxRoot (2 * N), hrootS⟩ =
      hexagonal.bufferedRoot j := by
    apply Subtype.ext
    have h := congrArg hexagonalRootFrame.symm hexagonalRootFrame_root
    simpa [phi, hexagonalBoxRoot, PeriodicGraph.bufferedRoot_val] using h.symm
  have hyBoundary : hexagonal.bufferedBoundary j (phi y) := by
    refine ⟨hexagonalRootFrame.symm z.1, ?_, ?_⟩
    · change hexagonalGraph.Adj (hexagonalRootFrame y.1.1)
        (hexagonalRootFrame z.1)
      exact (hexagonalRootFrame_adj _ _).2 hyz.1
    · intro hzOrbit
      have hzOrbit' :=
        (hexagonalRootFrame_mem_orbitBox_iff
          (hexagonal.bufferedRadius j) (hexagonalRootFrame.symm z.1)).2 hzOrbit
      exact hzOutside (by simpa using hzOrbit')
  change ocd_innerRestrict (hexagonalBufferedToBox j N (by omega)) omega ∈
    hexagonal.bufferedRootBoundaryEvent j
  refine ⟨phi y, hyBoundary, ?_⟩
  rwa [hroot] at hmapped

end StatMech.FK.PeriodicPlanar
