/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/LeafHallClose.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Lattice.HypercubicLattice.Part5
import Theorem.StatisticalMechanics.Code.Lattice.BoxSurfaceVolume.Part5
import Def.StatisticalMechanics.Code.Lattice.Clusters.Part7
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeane.Part5
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneUniqueness.Part3
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ForestLeafCountClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeRealiseClose.Part2
import Def.StatisticalMechanics.Code.Percolation.LeafHallClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem lhc_mem_trace {ω : ConfigSpace (Sym2 (Site d))} {n : ℕ} {x₀ z : Site d} :
    z ∈ lhc_trace ω n x₀ ↔ z ∈ vertexBoundary d n ∧ Connected d ω x₀ z := by
  classical
  rw [lhc_trace, Finset.mem_filter, tfc_mem_boundaryFinset]


theorem lhc_trace_card_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) (x₀ : Site d) :
    (lhc_trace ω n x₀).card ≤ boxSV_boundaryCard d n := by
  classical
  rw [← tfc_boundaryFinset_card]
  exact Finset.card_le_card (Finset.filter_subset _ _)


open Classical in


theorem lhc_two_le_trace_of_forestLeafSelection (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (x₀ : Site d)
    (hconn : ∀ x, x ∈ box d n → IsTrifurcation d ω x → Connected d ω x₀ x)
    (h : str_ForestLeafSelection ω n) :
    2 * Tcount d ω n ≤ (lhc_trace ω n x₀).card := by
  classical
  obtain ⟨r₀, ℓ, _hr₀, hℓbdry, hℓconn, _hℓr₀, hℓinj⟩ := h
  rw [← tfc_trifFinset_card]
  set T := tfc_trifFinset ω n with hT
  set ι := {x // x ∈ T} × Fin 2 with hι
  set f : ι → Site d := fun q => ℓ q.1.1 q.2 with hf
  
  have hfinj : Function.Injective f := by
    intro p q hpq
    have hp := tfc_mem_trifFinset.mp p.1.2
    have hq := tfc_mem_trifFinset.mp q.1.2
    obtain ⟨hxy, hjj⟩ := hℓinj p.1.1 hp.1 hp.2 q.1.1 hq.1 hq.2 p.2 q.2 hpq
    exact Prod.ext (Subtype.ext hxy) hjj
  
  have hfmem : ∀ q : ι, f q ∈ lhc_trace ω n x₀ := by
    intro q
    have hq := tfc_mem_trifFinset.mp q.1.2
    exact lhc_mem_trace.mpr ⟨hℓbdry q.1.1 hq.1 hq.2 q.2,
      (hconn q.1.1 hq.1 hq.2).trans (hℓconn q.1.1 hq.1 hq.2 q.2)⟩
  have hcardι : Fintype.card ι = 2 * T.card := by
    simp only [hι, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]; ring
  have hle := Finset.card_le_card_of_injOn (f := f) (s := (Finset.univ : Finset ι))
    (t := lhc_trace ω n x₀) (fun q _ => hfmem q) (fun p _ q _ hpq => hfinj hpq)
  rw [Finset.card_univ, hcardι] at hle
  omega


theorem lhc_twice_Tcount_succ_le_boundary (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (h : str_ForestLeafSelection ω n) :
    2 * Tcount d ω n + 1 ≤ boxSV_boundaryCard d n := by
  classical
  obtain ⟨r₀, ℓ, hr₀, hℓbdry, _hℓconn, hℓr₀, hℓinj⟩ := h
  rw [← tfc_trifFinset_card, ← tfc_boundaryFinset_card]
  set T := tfc_trifFinset ω n with hT
  set ι := Option ({x // x ∈ T} × Fin 2) with hι
  set f : ι → Site d := fun p => p.elim r₀ (fun q => ℓ q.1.1 q.2) with hf
  have hfinj : Function.Injective f := by
    intro p q hpq
    cases p with
    | none =>
      cases q with
      | none => rfl
      | some q' =>
          exact absurd hpq.symm
            ((tfc_mem_trifFinset.mp q'.1.2).elim (fun hb ht => hℓr₀ q'.1.1 hb ht q'.2))
    | some p' =>
      cases q with
      | none =>
          exact absurd hpq
            ((tfc_mem_trifFinset.mp p'.1.2).elim (fun hb ht => hℓr₀ p'.1.1 hb ht p'.2))
      | some q' =>
          have hp := tfc_mem_trifFinset.mp p'.1.2
          have hq := tfc_mem_trifFinset.mp q'.1.2
          obtain ⟨hxy, hjj⟩ := hℓinj p'.1.1 hp.1 hp.2 q'.1.1 hq.1 hq.2 p'.2 q'.2 hpq
          exact congrArg some (Prod.ext (Subtype.ext hxy) hjj)
  have hfmem : ∀ p : ι, f p ∈ tfc_boundaryFinset d n := by
    intro p
    cases p with
    | none => exact tfc_mem_boundaryFinset.mpr hr₀
    | some q' =>
        have hq := tfc_mem_trifFinset.mp q'.1.2
        exact tfc_mem_boundaryFinset.mpr (hℓbdry q'.1.1 hq.1 hq.2 q'.2)
  have hcardι : Fintype.card ι = 2 * T.card + 1 := by
    simp only [hι, Fintype.card_option, Fintype.card_prod, Fintype.card_fin, Fintype.card_coe]
    ring
  have hle := Finset.card_le_card_of_injOn (f := f) (s := (Finset.univ : Finset ι))
    (t := tfc_boundaryFinset d n) (fun p _ => hfmem p) (fun p _ q _ hpq => hfinj hpq)
  rw [Finset.card_univ, hcardι] at hle
  omega


end Percolation
end StatMech
