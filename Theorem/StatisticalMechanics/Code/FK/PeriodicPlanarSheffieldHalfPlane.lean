/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarSheffieldHalfPlane.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarSheffield.Part23
import Def.StatisticalMechanics.Code.FK.PeriodicPlanarSheffieldHalfPlane
open Filter MeasureTheory Set SimpleGraph Topology


namespace StatMech.FK.PeriodicPlanar

open BeffaraDC Lattice

variable {V : Type*} [DecidableEq V] [Countable V]
  {P : PeriodicGraph V}


theorem PeriodicGraph.connectedWithinSet_measurableSet
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    MeasurableSet (P.connectedWithinSet A x y) := by
  classical
  have heq : P.connectedWithinSet A x y =
      ⋃ l : List V, if
        (x :: l).getLast (List.cons_ne_nil _ _) = y ∧
          ∀ v ∈ x :: l, v ∈ A
        then {omega | List.IsChain (P.openSubgraph omega).Adj (x :: l)}
        else ∅ := by
    ext omega
    simp only [PeriodicGraph.connectedWithinSet, Set.mem_setOf_eq,
      Set.mem_iUnion]
    constructor
    · rintro ⟨l, hchain, hlast, hA⟩
      refine ⟨l, ?_⟩
      rw [if_pos ⟨hlast, hA⟩]
      exact hchain
    · rintro ⟨l, hl⟩
      split_ifs at hl with h
      · exact ⟨l, hl, h.1, h.2⟩
      · exact False.elim (by simpa using hl)
  rw [heq]
  exact MeasurableSet.iUnion fun l => by
    split_ifs
    · exact P.measurableSet_openChain_sheffield (x :: l)
    · exact MeasurableSet.empty

theorem PeriodicGraph.connectedWithinSet_isIncreasing
    (P : PeriodicGraph V) (A : Set V) (x y : V) :
    IsIncreasing (P.connectedWithinSet A x y) := by
  intro omega eta home
  rintro ⟨l, hchain, hlast, hA⟩
  refine ⟨l, hchain.imp ?_, hlast, hA⟩
  intro a b hab
  rw [P.openSubgraph_adj] at hab ⊢
  refine ⟨hab.1, Bool.eq_true_of_true_le ?_⟩
  simpa [hab.2] using home s(a, b)

theorem PeriodicGraph.connectedWithinSet_mono_region
    (P : PeriodicGraph V) {A B : Set V} (hAB : A ⊆ B) (x y : V) :
    P.connectedWithinSet A x y ⊆ P.connectedWithinSet B x y := by
  rintro omega ⟨l, hchain, hlast, hA⟩
  exact ⟨l, hchain, hlast, fun v hv => hAB (hA v hv)⟩


theorem PeriodicGraph.connectedWithinSet_configTranslate
    (P : PeriodicGraph V) (z : Site 2)
    (omega : ConfigSpace (Sym2 V)) (A : Set V) (x y : V) :
    P.configTranslate z omega ∈
        P.connectedWithinSet (P.shift z '' A) (P.shift z x) (P.shift z y) ↔
      omega ∈ P.connectedWithinSet A x y := by
  constructor
  · rintro ⟨l, hchain, hlast, hregion⟩
    let l₀ := l.map (P.shift (-z))
    refine ⟨l₀, ?_, ?_, ?_⟩
    · have hmap := List.isChain_map_of_isChain (P.shift (-z))
          (fun a b hab =>
            (P.openSubgraphTranslateHom (-z)
              (P.configTranslate z omega)).map_rel hab) hchain
      simpa [l₀] using hmap
    · calc
        (x :: l₀).getLast (List.cons_ne_nil _ _) =
            (P.shift (-z))
              ((P.shift z x :: l).getLast (List.cons_ne_nil _ _)) := by
                simpa [l₀] using
                  (List.getLast_map
                    (f := P.shift (-z))
                    (l := P.shift z x :: l) (by simp))
        _ = (P.shift (-z)) (P.shift z y) := congrArg (P.shift (-z)) hlast
        _ = y := P.shift_neg_shift z y
    · intro v hv
      have hvmap : P.shift z v ∈ P.shift z x :: l := by
        have := List.mem_map_of_mem (f := P.shift z) hv
        simpa [l₀, List.map_map, Function.comp_def] using this
      obtain ⟨a, ha, hav⟩ := hregion (P.shift z v) hvmap
      have hav' : a = v := (P.shift z).injective hav
      simpa only [hav'] using ha
  · rintro ⟨l, hchain, hlast, hregion⟩
    let lz := l.map (P.shift z)
    refine ⟨lz, ?_, ?_, ?_⟩
    · have hmap := List.isChain_map_of_isChain (P.shift z)
          (fun a b hab => (P.openSubgraphTranslateHom z omega).map_rel hab)
          hchain
      simpa [lz] using hmap
    · calc
        (P.shift z x :: lz).getLast (List.cons_ne_nil _ _) =
            P.shift z ((x :: l).getLast (List.cons_ne_nil _ _)) := by
              simpa [lz] using
                (List.getLast_map
                  (f := P.shift z) (l := x :: l) (by simp))
        _ = P.shift z y := congrArg (P.shift z) hlast
    · intro v hv
      change v ∈ P.shift z x :: l.map (P.shift z) at hv
      rcases List.mem_cons.mp hv with hv | hv
      · subst v
        exact ⟨x, hregion x (by simp), rfl⟩
      · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hv
        exact ⟨a, hregion a (by simp [ha]), rfl⟩


end StatMech.FK.PeriodicPlanar
