/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/InducedBC.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Foundations.ConfigSpace
import Theorem.StatisticalMechanics.Code.FK.RandomCluster.Part6
import Theorem.StatisticalMechanics.Code.FK.InfiniteVolume.Part7
import Theorem.StatisticalMechanics.Code.FK.MonoBC.Part4
import Theorem.StatisticalMechanics.Code.FK.DomainMarkov.Part5
import Theorem.StatisticalMechanics.Code.FK.WiredDominationInner.Part3
import Theorem.StatisticalMechanics.Code.FK.BoxCrossGraph.Part19
import Theorem.StatisticalMechanics.Code.FK.IvProperties
import Theorem.StatisticalMechanics.Code.Lattice.BoundaryConditions.Part10
import Def.StatisticalMechanics.Code.FK.InducedBC
open scoped BigOperators
open SimpleGraph

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false


namespace StatMech

namespace FK

open StatMech.Lattice

variable {d : ℕ}


theorem psiExt_innerEdge (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (e : Sym2 (boxVerts d n)) :
    psiExt d n ψ ω (innerEdge d n e) = ω e := by
  unfold psiExt
  have hmem : innerEdge d n e ∈ Set.range (innerEdge d n) := ⟨e, rfl⟩
  rw [dif_pos hmem]
  congr 1
  exact innerEdge_injective d n hmem.choose_spec


theorem psiExt_eq_psi_of_not_range (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) {e : Sym2 (boxVerts d (n+1))}
    (he : e ∉ Set.range (innerEdge d n)) : psiExt d n ψ ω e = ψ e := by
  unfold psiExt; rw [dif_neg he]


theorem psiExt_innerEdge_pair (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) (x y : boxVerts d n) :
    psiExt d n ψ ω s(boxVertIncl d n x, boxVertIncl d n y) = ω s(x, y) := by
  have h : s(boxVertIncl d n x, boxVertIncl d n y) = innerEdge d n s(x, y) := by
    rw [innerEdge, Sym2.map_mk]
  rw [h, psiExt_innerEdge]

@[simp] theorem innerRestrict_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) : innerRestrict d n (psiExt d n ψ ω) = ω := by
  funext e; rw [innerRestrict, psiExt_innerEdge]


theorem agreesOff_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1))))
    (ω : ConfigSpace (Sym2 (boxVerts d n))) :
    AgreesOff (innerEdgeFinset d n) ψ (psiExt d n ψ ω) := by
  intro e he
  rw [mem_innerEdgeFinset] at he
  exact psiExt_eq_psi_of_not_range d n ψ ω he


theorem psiExt_innerRestrict_of_agreesOff (d n : ℕ)
    {ψ ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))}
    (hρ : AgreesOff (innerEdgeFinset d n) ψ ρ) :
    psiExt d n ψ (innerRestrict d n ρ) = ρ := by
  funext e
  unfold psiExt
  split
  · rename_i hmem
    show innerRestrict d n ρ hmem.choose = ρ e
    rw [innerRestrict, hmem.choose_spec]
  · rename_i hmem
    have : e ∉ innerEdgeFinset d n := by rw [mem_innerEdgeFinset]; exact hmem
    exact (hρ e this).symm


theorem condFibre_eq_image_psiExt (d n : ℕ) (ψ : ConfigSpace (Sym2 (boxVerts d (n+1)))) :
    condFibre (innerEdgeFinset d n) ψ = Finset.univ.image (psiExt d n ψ) := by
  ext ρ
  rw [mem_condFibre, Finset.mem_image]
  constructor
  · intro hρ
    exact ⟨innerRestrict d n ρ, Finset.mem_univ _, psiExt_innerRestrict_of_agreesOff d n hρ⟩
  · rintro ⟨ω, _, rfl⟩
    exact agreesOff_psiExt d n ψ ω


end FK
end StatMech
