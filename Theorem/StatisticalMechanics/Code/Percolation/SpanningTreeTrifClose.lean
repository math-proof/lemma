/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/SpanningTreeTrifClose.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneMerge.Part4
import Theorem.StatisticalMechanics.Code.Percolation.TrifurcationCount.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BurtonKeaneClose2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve.Part5
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsProve2.Part3
import Theorem.StatisticalMechanics.Code.Percolation.DisjointArmEndsFinal.Part2
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.BKHallSDRClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.ArmEndDisjointClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.ForestAcyclicityClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.FacPairwiseClose
import Theorem.StatisticalMechanics.Code.Percolation.BKArmSelectorClose.Part2
import Theorem.StatisticalMechanics.Code.Percolation.RootedTreeSelectorClose
import Def.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


namespace StatMech

namespace Percolation

variable {d : ℕ}


theorem stt_reachable_iff (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (a b : {x : Site d // x ∈ tfc_trifFinset ω n}) :
    (stt_trifGraph ω n).Reachable a b ↔ Connected d ω a.1 b.1 := by
  constructor
  · intro h
    obtain ⟨w⟩ := h
    induction w with
    | nil => exact connected_rfl
    | cons hadj _ ih => exact hadj.2.trans ih
  · intro hc
    by_cases hab : a = b
    · exact hab ▸ Reachable.refl a
    · exact ⟨Walk.cons ⟨hab, hc⟩ Walk.nil⟩


theorem stt_lex_ne_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ ≠ a₂) :
    (toLex (a₁, b₁)) ≠ toLex (a₂, b₂) :=
  fun he => h (congrArg (fun p => (ofLex p).1) he)


theorem stt_lex_ne_snd {a b₁ b₂ : ℕ} (h : b₁ ≠ b₂) :
    (toLex (a, b₁)) ≠ toLex (a, b₂) :=
  fun he => h (by simpa using congrArg (fun p => (ofLex p).2) he)


theorem stt_lex_lt_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ < a₂) :
    (toLex (a₁, b₁)) < toLex (a₂, b₂) := by
  rw [Prod.Lex.toLex_lt_toLex]; exact Or.inl h


theorem stt_lex_not_lt_fst {a₁ a₂ b₁ b₂ : ℕ} (h : a₁ < a₂) :
    ¬ ((toLex (a₂, b₂)) < toLex (a₁, b₁)) := by
  rw [Prod.Lex.toLex_lt_toLex]; rintro (h1 | ⟨h1, h2⟩) <;> omega


open Classical in


theorem stt_exists_depthRank (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ) :
    ∃ rank : Site d → ℕ ×ₗ ℕ,
      ∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y := by
  classical
  
  obtain ⟨idx, hidx⟩ := (inferInstance : Countable (Site d)).exists_injective_nat
  
  obtain ⟨F, _hFle, _hFacyc, _hFreach⟩ :=
    (exists_isAcyclic_reachable_eq_le (G := stt_trifGraph ω n))
  
  set root : F.ConnectedComponent → {x : Site d // x ∈ tfc_trifFinset ω n} :=
    fun C => C.nonempty_supp.some with hroot
  
  set dep : Site d → ℕ := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then
      F.dist (root (F.connectedComponentMk ⟨v, hv⟩)) ⟨v, hv⟩
    else 0 with hdep
  refine ⟨fun v => toLex (dep v, idx v), ?_⟩
  
  intro x _hxbox _htri y _hybox _htriy hxy _hconn hrankeq
  
  have hidxeq : idx x = idx y := by simpa using congrArg (fun p => (ofLex p).2) hrankeq
  exact hxy (hidx hidxeq)


end Percolation
end StatMech
