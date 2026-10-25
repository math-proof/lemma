/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/Z2GaugeCycleComplete.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.Z2GaugeWilsonAffine.Part3
import Theorem.StatisticalMechanics.Code.Ising.KWClosedWalkParity.Part14
import Def.StatisticalMechanics.Code.FrontierA.Z2GaugeCycleComplete.Part6
open scoped BigOperators
open Finset SimpleGraph

set_option linter.unusedSectionVars false
set_option linter.unusedDecidableInType false
set_option linter.unusedFintypeInType false


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

noncomputable section

variable {V : Type*} [Fintype V] [DecidableEq V]
  (G : SimpleGraph V) [DecidableRel G.Adj]


@[simp] theorem mem_cycleCompleteEdgePreimage
    (delta : Finset (Sym2 V)) (p : G.edgeFinset) :
    p ∈ cycleCompleteEdgePreimage G delta ↔ p.1 ∈ delta := by
  simp [cycleCompleteEdgePreimage]

theorem cycleCompleteEdgeSet_preimage
    {delta : Finset (Sym2 V)} (hdelta : delta ⊆ G.edgeFinset) :
    cycleCompleteEdgeSet G (cycleCompleteEdgePreimage G delta) = delta := by
  ext e
  constructor
  · intro he
    rw [cycleCompleteEdgeSet, Finset.mem_map] at he
    obtain ⟨p, hp, rfl⟩ := he
    exact (mem_cycleCompleteEdgePreimage G delta p).mp hp
  · intro he
    rw [cycleCompleteEdgeSet, Finset.mem_map]
    exact ⟨⟨e, hdelta he⟩,
      (mem_cycleCompleteEdgePreimage G delta _).mpr he, rfl⟩

theorem cycleCompleteEdgePreimage_set (A : Finset G.edgeFinset) :
    cycleCompleteEdgePreimage G (cycleCompleteEdgeSet G A) = A := by
  ext p
  rw [mem_cycleCompleteEdgePreimage, cycleCompleteEdgeSet, Finset.mem_map]
  constructor
  · rintro ⟨q, hq, hqp⟩
    have : q = p := Subtype.ext hqp
    simpa [this] using hq
  · intro hp
    exact ⟨p, hp, rfl⟩

theorem cutSpace_member_subset {delta : Finset (Sym2 V)}
    (hdelta : delta ∈ cutSpace G) : delta ⊆ G.edgeFinset := by
  rw [cutSpace, Finset.mem_image] at hdelta
  obtain ⟨s, _, rfl⟩ := hdelta
  exact Finset.filter_subset _ _

theorem mem_cycleCompleteClosedFamily_iff [Nonempty V]
    (hG : G.Preconnected) (A : Finset G.edgeFinset) :
    A ∈ gaugeClosedSurfaceFamily (cycleCompleteIncidence G hG) ↔
      IsClosedPlaquetteSet (cycleCompleteIncidence G hG) A := by
  unfold gaugeClosedSurfaceFamily
  rw [Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨Finset.mem_powerset.mpr
      (by intro p hp; exact Finset.mem_attach _ _), h⟩


end
end StatMech.FrontierA
