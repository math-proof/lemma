/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TriangularSharpnessCritical.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.TriangularSharpnessThreshold
import Theorem.StatisticalMechanics.Code.FK.TriHexFKFiniteWiredCofinal.Part15
import Theorem.StatisticalMechanics.Code.OSSS.BetaCMatch.Part2
import Def.StatisticalMechanics.Code.FK.TriangularSharpnessCritical.Part4
open scoped BigOperators Classical
open Finset Set Filter Topology MeasureTheory SimpleGraph


namespace StatMech.FK.PeriodicPlanar

open StatMech.Lattice

open StatMech.OSSS

open RevealmentTranslation


theorem triangularBufferedToBox_injective (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    Function.Injective (triangularBufferedToBox j N hjn) := by
  intro x y h
  apply Subtype.ext
  exact congrArg (fun z : TriangularBoxVertex (2 * N) => (z : Site 2)) h

theorem triangularBufferedToBox_adjMatch (j N : Nat)
    (hjn : triangular.bufferedRadius j ≤ 2 * N) :
    ocd_AdjMatch (triangular.bufferedGraph j)
      (triangularBoxGraph (2 * N)) (triangularBufferedToBox j N hjn) := by
  intro x y
  rfl

theorem triangularBufferedToBox_not_outerBoundary
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (x : triangular.BufferedVertex j) :
    triangularBufferedToBox j N (by omega) x ∉
      triangularBoxShell (2 * N) (2 * N) := by
  intro hx
  have hxSmall : x.1 ∈ box 2 (2 * N - 1) := by
    rw [← triangular_mem_orbitBox_iff_box]
    exact triangular.orbitBox_mono (by omega) x.2
  exact (Finset.mem_filter.mp hx).2.2 hxSmall

theorem triangularBufferedToBox_inducedWiring_le
    (j N : Nat) (hjn : triangular.bufferedRadius j < N)
    (psi : ConfigSpace (Sym2 (TriangularBoxVertex (2 * N)))) :
    ocd_inducedWiring (triangularBoxGraph (2 * N))
        (triangularBufferedToBox j N (by omega))
        (fun y => y ∈ triangularBoxShell (2 * N) (2 * N)) psi ≤
      boundaryCliqueGraph (triangular.bufferedBoundary j) := by
  let incl := triangularBufferedToBox j N (by omega :
    triangular.bufferedRadius j ≤ 2 * N)
  apply StatMech.FK.ocd_comapInducedWiring_le triangularGraph incl
    (fun _ => rfl) (triangularBufferedToBox_injective j N (by omega))
    (fun y => y ∈ triangularBoxShell (2 * N) (2 * N))
    (triangular.bufferedBoundary j)
  · intro x
    exact triangularBufferedToBox_not_outerBoundary j N hjn x
  · intro x z hxz hz
    exact ⟨z, hxz, by
      intro hzOrbit
      exact hz hzOrbit⟩

theorem triangularCenteredShellFullEvent_subset_bufferedRestrict
    (j N : Nat) (hjn : triangular.bufferedRadius j < N) :
    triangularCenteredShellFullEvent (2 * N) N ⊆
      ocd_innerRestrict (triangularBufferedToBox j N (by omega)) ⁻¹'
        triangular.bufferedRootBoundaryEvent j := by
  intro omega hcross
  obtain ⟨v, hvShell, hreach⟩ := hcross
  let S : Set (TriangularBoxVertex (2 * N)) :=
    {x | x.1 ∈ triangular.orbitBox (triangular.bufferedRadius j)}
  have hrootS : triangularBoxRoot (2 * N) ∈ S := by
    change (0 : Site 2) ∈ triangular.orbitBox (triangular.bufferedRadius j)
    rw [triangular_mem_orbitBox_iff_box]
    simp
  have hvOutside : v ∉ S := by
    intro hvS
    have hvSmall : v.1 ∈ box 2 (N - 1) := by
      rw [← triangular_mem_orbitBox_iff_box]
      exact triangular.orbitBox_mono (by omega) hvS
    exact (Finset.mem_filter.mp hvShell).2.2 hvSmall
  obtain ⟨y, hyReach, z, hyz, hzOutside⟩ :=
    reachable_induce_innerBoundary
      (FK.openSub (triangularBoxGraph (2 * N)) omega) S
      hrootS hvOutside hreach
  let phi : ((FK.openSub (triangularBoxGraph (2 * N)) omega).induce S) →g
      FK.openSub (triangular.bufferedGraph j)
        (ocd_innerRestrict (triangularBufferedToBox j N (by omega)) omega) := {
    toFun := fun x => (⟨x.1.1, x.2⟩ : triangular.BufferedVertex j)
    map_rel' := by
      intro a b hab
      change triangularGraph.Adj a.1.1 b.1.1 ∧
        omega s(a.1, b.1) = true at hab
      rw [FK.openSub_adj]
      refine ⟨hab.1, ?_⟩
      simpa [ocd_innerRestrict, ocd_innerEdge, triangularBufferedToBox]
        using hab.2 }
  have hmapped := hyReach.map phi
  have hroot : phi ⟨triangularBoxRoot (2 * N), hrootS⟩ =
      triangular.bufferedRoot j := by
    apply Subtype.ext
    simp [phi, triangularBoxRoot, PeriodicGraph.bufferedRoot_val,
      triangular_root_eq_zero]
  have hyBoundary : triangular.bufferedBoundary j (phi y) := by
    refine ⟨z.1, ?_, ?_⟩
    · exact hyz.1
    · intro hzOrbit
      exact hzOutside hzOrbit
  change ocd_innerRestrict (triangularBufferedToBox j N (by omega)) omega ∈
    triangular.bufferedRootBoundaryEvent j
  refine ⟨phi y, hyBoundary, ?_⟩
  rwa [hroot] at hmapped

end StatMech.FK.PeriodicPlanar
