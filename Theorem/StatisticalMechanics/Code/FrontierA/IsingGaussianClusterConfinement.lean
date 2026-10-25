/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingGaussianClusterConfinement.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterDisentangling
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamWeightedFourCurrent
import Theorem.StatisticalMechanics.Code.Ising.FreeCorrelationDomainMonotonicity
import Def.StatisticalMechanics.Code.FrontierA.IsingGaussianClusterConfinement
open Finset SimpleGraph
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false


namespace StatMech.FrontierA

open StatMech.Sharpness

variable {V : Type*} [Fintype V] [DecidableEq V]


@[simp] theorem mem_finiteTreeSafeRegion
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) (v : V) :
    v ∈ finiteTreeSafeRegion G m roots ↔
      ∀ g ∈ roots, ¬ CurrentConnected G m g v := by
  simp [finiteTreeSafeRegion]

theorem finiteTreeSafeRegion_subset_compl
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) :
    finiteTreeSafeRegion G m roots ⊆ rootsᶜ := by
  intro v hv
  rw [Finset.mem_compl]
  intro hvroot
  exact (mem_finiteTreeSafeRegion G m roots v).mp hv v hvroot
    (CurrentConnected.refl G m v)

theorem finiteTreeSafeRegion_closed_of_connected
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots : Finset V) {u v : V}
    (hu : u ∈ finiteTreeSafeRegion G m roots)
    (huv : CurrentConnected G m u v) :
    v ∈ finiteTreeSafeRegion G m roots := by
  rw [mem_finiteTreeSafeRegion] at hu ⊢
  intro g hg hgv
  exact hu g hg (CurrentConnected.trans G hgv (CurrentConnected.symm G huv))


theorem finiteTreeSafeRegion_noCrossing
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m : Current V) (roots T : Finset V)
    (hev : finiteTreeSafeRegion G m roots = T) :
    NoCrossing G m T := by
  intro e he hpos
  obtain ⟨⟨u, v⟩, huv⟩ := e.exists_rep
  subst huv
  have hadj : G.Adj u v := by
    rw [mem_edgeFinset, mem_edgeSet] at he
    exact he
  by_cases hu : u ∈ T <;> by_cases hv : v ∈ T
  · left
    intro w hw
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption
  · exfalso
    have huvC : CurrentConnected G m u v := Adj.reachable ⟨hadj, hpos⟩
    have huSafe : u ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hu
    have hvNot : v ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hv
    rw [mem_finiteTreeSafeRegion] at huSafe hvNot
    push Not at hvNot
    obtain ⟨g, hg, hgv⟩ := hvNot
    exact huSafe g hg
      (CurrentConnected.trans G hgv (CurrentConnected.symm G huvC))
  · exfalso
    have hvuC : CurrentConnected G m v u :=
      Adj.reachable ⟨hadj.symm, by rwa [Sym2.eq_swap]⟩
    have hvSafe : v ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hv
    have huNot : u ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hu
    rw [mem_finiteTreeSafeRegion] at hvSafe huNot
    push Not at huNot
    obtain ⟨g, hg, hgu⟩ := huNot
    exact hvSafe g hg
      (CurrentConnected.trans G hgu (CurrentConnected.symm G hvuC))
  · right
    intro w hw
    rw [Finset.mem_compl]
    rw [Sym2.mem_iff] at hw
    rcases hw with rfl | rfl <;> assumption


theorem finiteTreeSafeRegion_congr
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (m m' : Current V) (roots T : Finset V)
    (hev : finiteTreeSafeRegion G m roots = T)
    (hagree : ∀ e ∈ G.edgeFinset, ¬ edgeInside T e -> m e = m' e) :
    finiteTreeSafeRegion G m' roots = T := by
  have hnm : NoCrossing G m T :=
    finiteTreeSafeRegion_noCrossing G m roots T hev
  have hnm' : NoCrossing G m' T := noCrossing_congr G m m' T hnm hagree
  have hsub := currentSubgraph_restrictCompl_congr G m m' T hagree
  ext v
  constructor
  · intro hvSafe
    by_contra hvT
    have hvNot : v ∉ finiteTreeSafeRegion G m roots := by simpa [hev] using hvT
    rw [mem_finiteTreeSafeRegion] at hvSafe hvNot
    push Not at hvNot
    obtain ⟨g, hg, hgv⟩ := hvNot
    have hgT : g ∉ T := by
      intro hgT
      have hgSafe : g ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hgT
      exact (mem_finiteTreeSafeRegion G m roots g).mp hgSafe g hg
        (CurrentConnected.refl G m g)
    have hgv' : CurrentConnected G m' g v := by
      apply (currentConnected_iff_compl G m' T hnm' g v hgT).mpr
      have hgvR := (currentConnected_iff_compl G m T hnm g v hgT).mp hgv
      unfold CurrentConnected
      rw [← hsub]
      exact hgvR
    exact hvSafe g hg hgv'
  · intro hvT
    rw [mem_finiteTreeSafeRegion]
    intro g hg hgv
    have hgT : g ∉ T := by
      intro hgT
      have hgSafe : g ∈ finiteTreeSafeRegion G m roots := by simpa [hev] using hgT
      exact (mem_finiteTreeSafeRegion G m roots g).mp hgSafe g hg
        (CurrentConnected.refl G m g)
    exact not_currentConnected_in_S G m' T hnm' g hgT v hvT hgv


end StatMech.FrontierA
