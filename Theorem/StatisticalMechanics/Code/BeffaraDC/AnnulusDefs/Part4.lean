/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/BeffaraDC/AnnulusDefs.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.TwoDim.Crossings.Part4
import Def.StatisticalMechanics.Code.BeffaraDC.AnnulusDefs.Part4
open Set
open StatMech.Lattice
open SimpleGraph


namespace StatMech

namespace BeffaraDC

@[simp]
theorem mem_annulusEvent {n N M : ℕ} {ω : ConfigSpace (Sym2 (Site 2))} :
    ω ∈ annulusEvent n N M ↔ AnnulusEvent ω n N M := Iff.rfl


theorem mapLe_isCircuit {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {x : Site 2} {w : (openSubgraph 2 ω).Walk x x} (hc : w.IsCircuit) :
    (w.mapLe (openSubgraph_mono h)).IsCircuit := by
  rw [Walk.isCircuit_def] at hc ⊢
  obtain ⟨ht, hne⟩ := hc
  refine ⟨?_, ?_⟩
  · show (Walk.map (Hom.ofLE (openSubgraph_mono h)) w).IsTrail
    rw [SimpleGraph.Walk.map_isTrail_iff_of_injective (fun _ _ hab => hab)]
    exact ht
  · show Walk.map (Hom.ofLE (openSubgraph_mono h)) w ≠ Walk.nil
    intro hcon
    apply hne
    cases w with
    | nil => rfl
    | cons hadj rest => simp [Walk.map] at hcon


theorem mapLe_support {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {x : Site 2} (w : (openSubgraph 2 ω).Walk x x) :
    (w.mapLe (openSubgraph_mono h)).support = w.support := by
  show (Walk.map (Hom.ofLE (openSubgraph_mono h)) w).support = w.support
  rw [Walk.support_map]
  apply List.map_id''
  intro _; rfl


theorem IsAnnulusCircuit.mono {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {n N : ℕ} {x : Site 2} {w : (openSubgraph 2 ω).Walk x x}
    (hw : IsAnnulusCircuit ω n N w) :
    IsAnnulusCircuit ω' n N (w.mapLe (openSubgraph_mono h)) := by
  refine ⟨mapLe_isCircuit h hw.1, ?_⟩
  intro y hy
  rw [mapLe_support h w] at hy
  exact hw.2 y hy


theorem annulusEvent_increasing {ω ω' : ConfigSpace (Sym2 (Site 2))} (h : ω ≤ ω')
    {n N M : ℕ} (hω : ω ∈ annulusEvent n N M) : ω' ∈ annulusEvent n N M := by
  obtain ⟨x, w, hcirc, hsep, y, hyM, hyM', hconn⟩ := hω
  refine ⟨x, w.mapLe (openSubgraph_mono h), hcirc.mono h, ?_, y, hyM, hyM', ?_⟩
  · rw [show {z | z ∈ (w.mapLe (openSubgraph_mono h)).support} = {z | z ∈ w.support}
        from by rw [mapLe_support h w]]
    exact hsep
  · exact hconn.mono (openSubgraph_mono h)


end BeffaraDC
end StatMech
