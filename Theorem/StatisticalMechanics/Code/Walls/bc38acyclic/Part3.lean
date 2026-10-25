/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc38acyclic.lean -/

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
import Theorem.StatisticalMechanics.Code.Percolation.BKForestLib.Part6
import Theorem.StatisticalMechanics.Code.Percolation.ForestSelectorProve.Part7
import Theorem.StatisticalMechanics.Code.Percolation.RootedForestPeelClose.Part4
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeArmClose.Part3
import Theorem.StatisticalMechanics.Code.Percolation.SpanningTreeTrifClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc26forest.Part3
import Theorem.StatisticalMechanics.Code.Walls.bc35globalarm
import Theorem.StatisticalMechanics.Code.Walls.bc36rooteddiv.Part2
import Theorem.StatisticalMechanics.Code.Walls.bc37armadj.Part5
import Def.StatisticalMechanics.Code.Walls.bc38acyclic.Part2
open Set SimpleGraph Finset MeasureTheory
open scoped BigOperators ENNReal NNReal

open StatMech.Lattice StatMech.ConfigSpace


set_option linter.style.longLine false


namespace StatMech.Walls

open StatMech.Percolation

variable {d : ℕ}


theorem bc38_exists_rootedArmForest (ω : ConfigSpace (Sym2 (Site d))) (n : ℕ)
    (hspan : bc38_ArmAdjSpanning ω n) :
    ∃ (rank : Site d → ℕ ×ₗ ℕ) (par : Site d → Site d),
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x ≠ rank y) ∧
      (∀ x, x ∈ box d n → IsTrifurcation d ω x → ∀ y, y ∈ box d n → IsTrifurcation d ω y →
        x ≠ y → Connected d ω x y → rank x < rank y →
          bc37_ArmAdjacent ω n y (par y) ∧ rank (par y) < rank y) := by
  classical
  set G := bc37_armAdjGraph ω n with hG
  obtain ⟨idx, hidx⟩ := (inferInstance : Countable (Site d)).exists_injective_nat
  set root : {x : Site d // x ∈ tfc_trifFinset ω n} → {x : Site d // x ∈ tfc_trifFinset ω n} :=
    fun v => (G.connectedComponentMk v).nonempty_supp.some with hroot
  have hrr : ∀ v, G.Reachable (root v) v := by
    intro v; rw [← SimpleGraph.ConnectedComponent.eq]
    exact (G.connectedComponentMk v).nonempty_supp.some_mem
  have hroot_inv : ∀ v w, G.Reachable v w → root v = root w := by
    intro v w hvw
    have : G.connectedComponentMk v = G.connectedComponentMk w :=
      SimpleGraph.ConnectedComponent.eq.mpr hvw
    simp only [hroot, this]
  set dep : Site d → ℕ := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then G.dist (root ⟨v, hv⟩) ⟨v, hv⟩ else 0 with hdep
  set par : Site d → Site d := fun v =>
    if hv : v ∈ tfc_trifFinset ω n then (bc38_parentTo G root ⟨v, hv⟩).1 else v with hpar
  have hdep0 : ∀ (v : Site d) (hv : v ∈ tfc_trifFinset ω n),
      dep v = 0 ↔ (⟨v, hv⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨v, hv⟩ := by
    intro v hv
    simp only [hdep, dif_pos hv]
    rw [SimpleGraph.dist_eq_zero_iff_eq_or_not_reachable]
    constructor
    · rintro (h | h); · exact h.symm
      · exact absurd (hrr ⟨v, hv⟩) h
    · intro h; exact Or.inl h.symm
  refine ⟨fun v => toLex (dep v, idx v), par, ?_, ?_⟩
  · 
    intro x _hxbox _htri y _hybox _htriy hxy _hconn hrankeq
    have hidxeq : idx x = idx y := by simpa using congrArg (fun p => (ofLex p).2) hrankeq
    exact hxy (hidx hidxeq)
  · 
    intro x hxbox htri y hybox htriy hxy hconn hlt
    have hxT : x ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hxbox, htri⟩
    have hyT : y ∈ tfc_trifFinset ω n := tfc_mem_trifFinset.mpr ⟨hybox, htriy⟩
    simp only at hlt
    
    have hxyreach : G.Reachable ⟨x, hxT⟩ ⟨y, hyT⟩ := hspan ⟨x, hxT⟩ ⟨y, hyT⟩ hconn
    have hrootxy : root ⟨x, hxT⟩ = root ⟨y, hyT⟩ := hroot_inv _ _ hxyreach
    
    have hynonroot : (⟨y, hyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) ≠ root ⟨y, hyT⟩ := by
      intro hyroot
      have hdepy0 : dep y = 0 := (hdep0 y hyT).mpr hyroot
      rw [hdepy0, Prod.Lex.toLex_lt_toLex] at hlt
      have hdepx0 : dep x = 0 := by rcases hlt with h | ⟨h, _⟩; · omega
                                    · exact h
      have hxroot : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = root ⟨x, hxT⟩ :=
        (hdep0 x hxT).mp hdepx0
      apply hxy
      have hxy_eq : (⟨x, hxT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n}) = ⟨y, hyT⟩ := by
        rw [hxroot, hrootxy, ← hyroot]
      exact congrArg Subtype.val hxy_eq
    obtain ⟨hadj, hdlt⟩ := bc38_parentTo_spec G root hynonroot (hrr ⟨y, hyT⟩)
    have hpary : par y = (bc38_parentTo G root ⟨y, hyT⟩).1 := by simp only [hpar, dif_pos hyT]
    have hparyT : par y ∈ tfc_trifFinset ω n := by
      rw [hpary]; exact (bc38_parentTo G root ⟨y, hyT⟩).2
    
    have hpar_pack : (⟨par y, hparyT⟩ : {x : Site d // x ∈ tfc_trifFinset ω n})
        = bc38_parentTo G root ⟨y, hyT⟩ := Subtype.ext hpary
    refine ⟨?_, ?_⟩
    · 
      have : G.Adj ⟨y, hyT⟩ ⟨par y, hparyT⟩ := by rw [hpar_pack]; exact hadj
      exact this
    · 
      have hyparreach : G.Reachable ⟨y, hyT⟩ (bc38_parentTo G root ⟨y, hyT⟩) := hadj.reachable
      have hrootpary : root (bc38_parentTo G root ⟨y, hyT⟩) = root ⟨y, hyT⟩ :=
        hroot_inv _ _ hyparreach.symm
      have hdeppary : dep (par y) = G.dist (root ⟨y, hyT⟩) (bc38_parentTo G root ⟨y, hyT⟩) := by
        simp only [hdep, dif_pos hparyT]
        rw [hpar_pack, hrootpary]
      have hdepy : dep y = G.dist (root ⟨y, hyT⟩) ⟨y, hyT⟩ := by simp only [hdep, dif_pos hyT]
      have hdeplt : dep (par y) < dep y := by rw [hdeppary, hdepy]; exact hdlt
      exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl hdeplt)


end StatMech.Walls
