/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Lattice/JordanOrbitCycle.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.JordanClusterBridge.Part8
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosure.Part6
import Theorem.StatisticalMechanics.Code.Lattice.MinimalPeriodLoop.Part2
import Theorem.StatisticalMechanics.Code.Lattice.UmlaufsatzSingleCycle.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchDual.Part4
import Theorem.StatisticalMechanics.Code.Lattice.NoPinchMatching.Part2
import Theorem.StatisticalMechanics.Code.Lattice.Wall1EmbeddingRetry
import Theorem.StatisticalMechanics.Code.Lattice.NoDiagTouchClose.Part4
import Theorem.StatisticalMechanics.Code.Lattice.CornerBalance.Part4
import Theorem.StatisticalMechanics.Code.Lattice.EarRemoval.Part5
import Def.StatisticalMechanics.Code.Lattice.JordanOrbitCycle.Part2
open SimpleGraph Set Function


namespace StatMech

namespace Lattice

theorem joc_Ltromino_kingSaturated : npm_KingSaturated joc_Ltromino := by
  intro f
  simp only [joc_Ltromino, npd_P00, npd_P11, npd_P10, npd_P01, Set.mem_insert_iff,
    Set.mem_singleton_iff, site2_eq]
  refine ⟨fun h1 h2 => ?_, fun h1 h2 => ?_⟩ <;>
    (rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;> omega)


theorem joc_Ltromino_faceMultiplicityOne
    (a : {e : Dart // IsBoundaryDart joc_Ltromino e}) :
    usc_FaceMultiplicityOne joc_Ltromino a :=
  emb_faceMultiplicityOne_of_kingSaturated joc_Ltromino a joc_Ltromino_kingSaturated


theorem joc_diagK_diagTouch : npd_DiagTouch jcb_diagK (![0, 0] : Site 2) :=
  npd_diagTouch_example


theorem joc_diagK_not_kingSaturated : ¬ npm_KingSaturated jcb_diagK :=
  npm_diagTouch_not_kingSaturated joc_diagK_diagTouch


theorem joc_pinch_forces_diagTouch {K : Set (Site 2)} {e₁ e₂ : Dart}
    (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) (hdir : e₁.dir ≠ e₂.dir) :
    npd_DiagTouch K (dartFace e₁) :=
  npd_pinch_forces_diagTouch he₁ he₂ hface hdir


theorem joc_noLocalPinch_of_kingSaturated {K : Set (Site 2)} (hks : npm_KingSaturated K)
    {e₁ e₂ : Dart} (he₁ : IsBoundaryDart K e₁) (he₂ : IsBoundaryDart K e₂)
    (hface : dartFace e₁ = dartFace e₂) : e₁.dir = e₂.dir := by
  have hnt : npd_NoDiagTouch K := npm_noDiagTouch_of_kingSaturated hks
  exact npd_noPinch_local_of_noDiagTouch he₁ he₂ hface (hnt (dartFace e₁))


theorem joc_status :
    (∀ (v : Site 2) (c : (hypercubicLattice 2).Walk v v) (hc : c.IsCycle),
        Nat.card (jcb_BoundedRegion (joc_cycleSubgraph c hc)) = 1) ∧
    (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}),
        npm_KingSaturated K →
        Set.InjOn (fun k => dartFace ((dartNext K)^[k] a.1)) (Set.Iio (dartOrbitPeriod K a))) ∧
    (∀ (K : Set (Site 2)) (a : {e : Dart // IsBoundaryDart K e}),
        3 ≤ dartOrbitPeriod K a → npm_KingSaturated K → (mpl_orbitLoop K a).IsCycle) ∧
    ¬ npm_KingSaturated jcb_diagK ∧
    npd_DiagTouch jcb_diagK (![0, 0] : Site 2) :=
  ⟨fun _ c hc => joc_cycle_uniqueBoundedRegion c hc,
   fun K a => joc_faceInjOn_of_kingSaturated K a,
   fun K a => joc_kingSaturated_orbitLoop_isCycle K a,
   joc_diagK_not_kingSaturated,
   joc_diagK_diagTouch⟩

end Lattice
end StatMech
