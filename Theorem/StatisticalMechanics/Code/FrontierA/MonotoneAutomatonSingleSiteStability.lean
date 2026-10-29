/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/MonotoneAutomatonSingleSiteStability.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.MonotoneAutomatonNearestConclusion.Part2
open Set
open scoped NNReal


namespace StatMech.FrontierA

open StatMech.Lattice StatMech.Percolation StatMech.ConfigSpace

variable {d : ℕ}


theorem siteOpenGraph_mono {eta eta' : ConfigSpace (Site d)} (h : eta ≤ eta') :
    siteOpenGraph eta ≤ siteOpenGraph eta' := by
  intro x y hxy
  refine ⟨hxy.1, ?_, ?_⟩
  · exact Bool.eq_true_of_true_le (hxy.2.1 ▸ h x)
  · exact Bool.eq_true_of_true_le (hxy.2.2 ▸ h y)


theorem le_raiseField (xi : NonnegativeField d) (x : Site d) (r : NNReal) :
    xi ≤ raiseField xi x r := by
  intro y
  by_cases hy : y = x
  · subst y
    simp [raiseField]
  · simp [raiseField, hy]


theorem site_eq_true_of_siteCluster_infinite
    (eta : ConfigSpace (Site d)) (x : Site d)
    (hinf : (siteCluster eta x).Infinite) :
    eta x = true := by
  by_contra hx
  have hxfalse : eta x = false := by
    cases h : eta x
    · rfl
    · exact (hx h).elim
  have hsub : siteCluster eta x ⊆ ({x} : Set (Site d)) := by
    intro y hy
    rcases hy with ⟨w⟩
    cases w with
    | nil => simp
    | cons hadj w =>
        exfalso
        simpa [hxfalse] using hadj.2.1
  exact hinf (Set.finite_singleton x |>.subset hsub)


theorem siteCluster_raise_eq_of_infinite_of_not_mem
    (T : MonotoneAutomaton d) (xi : NonnegativeField d)
    (x y : Site d) (r : NNReal)
    (hinf : (siteCluster (T (raiseField xi x r)) y).Infinite)
    (hx : x ∉ siteCluster (T (raiseField xi x r)) y) :
    siteCluster (T (raiseField xi x r)) y = siteCluster (T xi) y := by
  let etaRaised : ConfigSpace (Site d) := T (raiseField xi x r)
  let etaBase : ConfigSpace (Site d) := T xi
  have heta : etaBase ≤ etaRaised := T.monotone (le_raiseField xi x r)
  apply Set.Subset.antisymm
  · intro z hz
    rcases hz with ⟨w⟩
    have hvertexBase : ∀ a : Site d, a ∈ siteCluster etaRaised y →
        etaBase a = true := by
      intro a ha
      have hax : a ∉ siteCluster etaRaised x := by
        intro hxa
        apply hx
        exact ha.trans hxa.symm
      exact site_eq_true_of_siteCluster_infinite etaBase a
        (T.otherInfiniteClustersStable xi x r a hax (by
          rw [show siteCluster etaRaised a = siteCluster etaRaised y by
            ext z
            constructor
            · exact fun haz => ha.trans haz
            · exact fun hyz => ha.symm.trans hyz]
          exact hinf))
    have hwalk : ∀ {a b : Site d},
        (siteOpenGraph etaRaised).Walk a b →
        a ∈ siteCluster etaRaised y →
        (siteOpenGraph etaBase).Walk a b := by
      intro a b p
      induction p with
      | nil =>
          intro _
          exact SimpleGraph.Walk.nil
      | @cons a b c hab p ih =>
          intro ha
          have hb : b ∈ siteCluster etaRaised y :=
            ha.trans hab.reachable
          exact SimpleGraph.Walk.cons
            ⟨hab.1, hvertexBase a ha, hvertexBase b hb⟩ (ih hb)
    exact ⟨hwalk w (by exact ⟨SimpleGraph.Walk.nil⟩)⟩
  · intro z hz
    exact (SimpleGraph.Reachable.mono (siteOpenGraph_mono heta) hz)


end StatMech.FrontierA
