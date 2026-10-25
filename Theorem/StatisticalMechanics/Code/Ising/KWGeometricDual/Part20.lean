/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KWGeometricDual.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib.Combinatorics.Graph.Basic
import Theorem.StatisticalMechanics.Code.Lattice.JordanEnclosureDuality.Part4
import Theorem.StatisticalMechanics.Code.Lattice.PeierlsHoleFreeBoundary.Part4
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierClose.Part2
import Theorem.StatisticalMechanics.Code.Walls.fwrfaceregion.Part3
import Instance.StatisticalMechanics.Code.Ising.KWGeometricDual.Part7
open scoped BigOperators
open Finset SimpleGraph Set


namespace StatMech

namespace Ising

open StatMech.Lattice

open StatMech.Walls


theorem kwg_subdivGraph_port_degree {V E : Type*} [Finite V] [Finite E]
    [DecidableEq V] [DecidableEq E]
    (ends : E → Sym2 V) (e : E) (b : Bool) :
    (kwg_subdivGraph ends).degree (Sum.inr (e, b)) = 2 := by
  classical
  letI : SimpleGraph.LocallyFinite (kwg_subdivGraph ends) :=
    kwg_subdivGraph_locallyFinite ends
  letI : Fintype ((kwg_subdivGraph ends).neighborSet (Sum.inr (e, b))) :=
    Fintype.ofFinite _
  rw [SimpleGraph.degree]
  apply Finset.card_eq_two.mpr
  let v : V := if b then (ends e).out.2 else (ends e).out.1
  refine ⟨Sum.inl v, Sum.inr (e, !b), ?_, ?_⟩
  · simp [v]
  · ext z
    rcases z with w | ⟨e', b'⟩
    · cases b <;> simp [v, kwg_subdivGraph]
    · cases b <;> cases b' <;> simp [kwg_subdivGraph, eq_comm]


theorem kwg_subdivGraph_face_degree {V E : Type*} [Fintype V] [Fintype E]
    [DecidableEq V] [DecidableEq E] (ends : E → Sym2 V) (v : V) :
    (kwg_subdivGraph ends).degree (Sum.inl v) =
      ((Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)).card +
      ((Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)).card := by
  classical
  let A := (Finset.univ : Finset E).filter (fun e => (ends e).out.1 = v)
  let B := (Finset.univ : Finset E).filter (fun e => (ends e).out.2 = v)
  let p0 : E → kwg_SubdivVertex V E := fun e => Sum.inr (e, false)
  let p1 : E → kwg_SubdivVertex V E := fun e => Sum.inr (e, true)
  have hnb : (kwg_subdivGraph ends).neighborFinset (Sum.inl v) = A.image p0 ∪ B.image p1 := by
    ext z
    rcases z with w | ⟨e, b⟩
    · simp [A, B, p0, p1, kwg_subdivGraph]
    · cases b <;> simp [A, B, p0, p1, kwg_subdivGraph, eq_comm]
  have hp0 : Function.Injective p0 := by
    intro a b h
    simpa [p0] using h
  have hp1 : Function.Injective p1 := by
    intro a b h
    simpa [p1] using h
  rw [← SimpleGraph.card_neighborFinset_eq_degree, hnb,
    Finset.card_union_of_disjoint]
  · rw [Finset.card_image_of_injective A hp0,
      Finset.card_image_of_injective B hp1]
  · rw [Finset.disjoint_left]
    intro z hz0 hz1
    obtain ⟨e0, _, rfl⟩ := Finset.mem_image.mp hz0
    obtain ⟨e1, _, h⟩ := Finset.mem_image.mp hz1
    simp [p0, p1] at h

theorem kwg_card_filter_eq_sum_ite {E : Type*} [DecidableEq E]
    (F : Finset E) (p : E → Prop) [DecidablePred p] :
    (F.filter p).card = ∑ e ∈ F, if p e then 1 else 0 := by
  classical
  induction F using Finset.induction with
  | empty => simp
  | @insert e F he ih =>
      by_cases hp : p e <;> simp [he, hp, ih]


theorem kwg_sum_degree_even {V E : Type*} [Fintype V] [DecidableEq V]
    [DecidableEq E] (ends : E → Sym2 V) (F : Finset E) :
    Even (∑ v : V, kwg_degree ends F v) := by
  classical
  unfold kwg_degree
  simp_rw [kwg_card_filter_eq_sum_ite]
  rw [Finset.sum_comm]
  apply Finset.even_sum
  intro e he
  rw [← kwg_card_filter_eq_sum_ite (Finset.univ : Finset V)
    (fun v => kwg_incidentMod2 v (ends e))]
  induction ends e using Sym2.inductionOn with
  | _ x y =>
      by_cases hxy : x = y
      · subst y
        simp [kwg_incidentMod2_mk]
      · have hfilter : (Finset.univ : Finset V).filter
            (fun v => kwg_incidentMod2 v s(x, y)) = {x, y} := by
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and,
            kwg_incidentMod2_mk, Finset.mem_insert, Finset.mem_singleton]
          constructor
          · rintro (⟨hx, _⟩ | ⟨hy, _⟩)
            · exact Or.inl hx.symm
            · exact Or.inr hy.symm
          · rintro (hx | hy)
            · exact Or.inl ⟨hx.symm, fun hyv => hxy (hx.symm.trans hyv.symm)⟩
            · exact Or.inr ⟨hy.symm, fun hxv => hxy (hxv.trans hy)⟩
        rw [hfilter, Finset.card_pair hxy]
        exact ⟨1, rfl⟩


end Ising
end StatMech
