/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWClosedWalkParity.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut.Part8
import Theorem.StatisticalMechanics.Code.Lattice.CrossingParity.Part2
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsContourFinal.Part4
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section Coboundary

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


theorem walkParity_eq_xor_of_isCoboundary {δ : Finset (Sym2 V)} (c : V → Bool)
    (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v))
    {x y : V} (p : Gp.Walk x y) :
    walkParity Gp δ p = (c x).xor (c y) := by
  induction p with
  | nil => simp
  | @cons u v w h q ih =>
    rw [walkParity_cons, ih]
    
    have hedge : decide (s(u, v) ∈ δ) = (c u).xor (c v) := by
      have : decide (s(u, v) ∈ δ) = decide (c u ≠ c v) := decide_eq_decide.mpr (hδ h)
      rw [this]
      cases c u <;> cases c v <;> simp
    rw [hedge]
    
    cases c u <;> cases c v <;> cases c w <;> rfl

end Coboundary


section ForwardHandshake

variable {V : Type*} [DecidableEq V] {Gp : SimpleGraph V}


theorem evenOnCycles_of_isCoboundary [Fintype V] [DecidableRel Gp.Adj]
    {δ : Finset (Sym2 V)} (c : V → Bool)
    (hδ : ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v)) :
    EvenOnCycles Gp δ := by
  intro x p
  rw [walkParity_eq_xor_of_isCoboundary c hδ p]
  cases c x <;> rfl

omit [DecidableEq V] in


theorem cutEdges_isCoboundary [Fintype V] [DecidableRel Gp.Adj] (s : ConfigSpace V)
    {u v : V} (h : Gp.Adj u v) : s(u, v) ∈ cutEdges Gp s ↔ s u ≠ s v :=
  mem_cutEdges_iff Gp s h


theorem evenOnCycles_cutEdges [Fintype V] [DecidableRel Gp.Adj] (s : ConfigSpace V) :
    EvenOnCycles Gp (cutEdges Gp s) :=
  evenOnCycles_of_isCoboundary s (fun h => cutEdges_isCoboundary s h)


theorem evenOnCycles_of_mem_cutSpace [Fintype V] [DecidableRel Gp.Adj]
    {δ : Finset (Sym2 V)} (hδ : δ ∈ cutSpace Gp) : EvenOnCycles Gp δ := by
  rw [cutSpace, Finset.mem_image] at hδ
  obtain ⟨s, _, rfl⟩ := hδ
  exact evenOnCycles_cutEdges s

end ForwardHandshake


section Equivalence

variable {V : Type*} [Fintype V] [DecidableEq V]
  {Gp : SimpleGraph V} [DecidableRel Gp.Adj]


theorem evenOnCycles_iff_mem_cutSpace [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} (hδsub : δ ⊆ Gp.edgeFinset) :
    EvenOnCycles Gp δ ↔ δ ∈ cutSpace Gp :=
  ⟨fun hev => mem_cutSpace_of_evenOnCycles hG hδsub hev, evenOnCycles_of_mem_cutSpace⟩


theorem isCoboundary_iff_mem_cutSpace [Nonempty V] (hG : Gp.Preconnected)
    {δ : Finset (Sym2 V)} (hδsub : δ ⊆ Gp.edgeFinset) :
    (∃ c : V → Bool, ∀ {u v : V}, Gp.Adj u v → (s(u, v) ∈ δ ↔ c u ≠ c v))
      ↔ δ ∈ cutSpace Gp := by
  constructor
  · rintro ⟨c, hc⟩
    exact (evenOnCycles_iff_mem_cutSpace hG hδsub).mp (evenOnCycles_of_isCoboundary c hc)
  · intro hδ
    rw [cutSpace, Finset.mem_image] at hδ
    obtain ⟨s, _, rfl⟩ := hδ
    exact ⟨s, fun h => cutEdges_isCoboundary s h⟩

end Equivalence
end Ising
end StatMech
