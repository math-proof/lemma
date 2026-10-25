/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/FiniteCurrentParityLift.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierB.FiniteCurrentParity.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.BackboneSupportLexParityBridge.Part7
import Def.StatisticalMechanics.Code.FrontierB.FiniteCurrentParityLift
open MeasureTheory
open scoped BigOperators ENNReal


namespace StatMech.FrontierB

open Sharpness Ising

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]

omit [DecidableEq V] in
@[simp] theorem mem_currentParitySupport (m : EdgeCurrent G)
    (e : G.edgeFinset) : e.1 ∈ currentParitySupport G m ↔ Odd (m e) := by
  simp [currentParitySupport]

omit [DecidableEq V] in
theorem currentParitySupport_subset (m : EdgeCurrent G) :
    currentParitySupport G m ⊆ G.edgeFinset := by
  intro e he
  obtain ⟨f, hf, rfl⟩ := Finset.mem_map.1 he
  exact f.2

theorem currentParitySupport_eq_iff
    (H : Finset (Sym2 V)) (hH : H ⊆ G.edgeFinset)
    (m : EdgeCurrent G) :
    currentParitySupport G m = H ↔
      ∀ e : G.edgeFinset, if e.1 ∈ H then Odd (m e) else Even (m e) := by
  constructor
  · intro h e
    by_cases he : e.1 ∈ H
    · simp only [if_pos he]
      rw [← h] at he
      simpa using he
    · simp only [if_neg he]
      rw [← Nat.not_odd_iff_even]
      intro ho
      apply he
      rw [← h]
      simpa using ho
  · intro h
    ext e
    by_cases heG : e ∈ G.edgeFinset
    · let es : G.edgeFinset := ⟨e, heG⟩
      change (es.1 ∈ currentParitySupport G m ↔ e ∈ H)
      rw [mem_currentParitySupport]
      by_cases heH : e ∈ H
      · have ho : Odd (m es) := by simpa [es, heH] using h es
        simp [heH, ho]
      · have hev : Even (m es) := by simpa [es, heH] using h es
        rw [← Nat.not_odd_iff_even] at hev
        simp [heH, hev]
    · have heH : e ∉ H := fun he => heG (hH he)
      constructor
      · intro he
        exact (heG (currentParitySupport_subset G m he)).elim
      · intro he
        exact (heH he).elim

theorem sources_eq_sources_currentParitySupport (m : EdgeCurrent G) :
    sources G (ofEdgeFun G m) =
      sources G (edgeIndicatorCurrent (currentParitySupport G m)) := by
  ext v
  rw [Sharpness.mem_sources, Sharpness.mem_sources,
    incidentFlux_edgeIndicatorCurrent G (currentParitySupport G m)
      (currentParitySupport_subset G m)]
  let E := G.edgeFinset.filter (fun e => v ∈ e)
  have hfilter :
      E.filter (fun e => Odd (ofEdgeFun G m e)) =
        (currentParitySupport G m).filter (fun e => v ∈ e) := by
    ext e
    simp only [E, Finset.mem_filter]
    constructor
    · rintro ⟨⟨heG, hev⟩, ho⟩
      exact ⟨mem_currentParitySupport G m ⟨e, heG⟩ |>.2 (by
        simpa [ofEdgeFun, heG] using ho), hev⟩
    · rintro ⟨he, hev⟩
      have heG := currentParitySupport_subset G m he
      exact ⟨⟨heG, hev⟩, by
        simpa [ofEdgeFun, heG] using
          (mem_currentParitySupport G m ⟨e, heG⟩ |>.1 he)⟩
  unfold Sharpness.incidentFlux incCount
  rw [Finset.odd_sum_iff_odd_card_odd]
  exact iff_of_eq (congrArg Odd (congrArg Finset.card hfilter))

theorem sources_empty_iff_currentParitySupport_even (m : EdgeCurrent G) :
    sources G (ofEdgeFun G m) = ∅ ↔
      IsEvenSubgraph (currentParitySupport G m) := by
  rw [sources_eq_sources_currentParitySupport G m]
  constructor
  · intro hsrc v
    have hv : v ∉ sources G (edgeIndicatorCurrent (currentParitySupport G m)) := by
      rw [hsrc]
      simp
    rw [Sharpness.mem_sources,
      incidentFlux_edgeIndicatorCurrent G (currentParitySupport G m)
        (currentParitySupport_subset G m)] at hv
    exact Nat.not_odd_iff_even.1 hv
  · intro heven
    apply sources_edgeIndicatorCurrent G (currentParitySupport G m) ∅
      (currentParitySupport_subset G m)
    exact (hasOddBoundary_empty _).2 heven

end StatMech.FrontierB
