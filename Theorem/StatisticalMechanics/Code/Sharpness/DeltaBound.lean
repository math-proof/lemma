/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/DeltaBound.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Sharpness.Claim1IsingComplete.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.SwitchingDichotomy.Part2
import Theorem.StatisticalMechanics.Code.Ising.TwoReplica.Part7
open SimpleGraph Finset
open scoped BigOperators symmDiff
open Classical

set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000


namespace StatMech

namespace Sharpness

open FluxEdgeCopy

variable {V : Type*} [Fintype V] [DecidableEq V]

variable (G : SimpleGraph V) [DecidableRel G.Adj]


theorem summable_gatedSourcePairSummand (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P] :
    Summable (fun pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0)) := by
  have hprod : Summable (fun pq :
      (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ) =>
      ‖(if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0)‖ *
        ‖(if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0)‖) :=
    Summable.mul_of_nonneg
      (summable_norm_currentSum_summand G β J A)
      (summable_norm_currentSum_summand G β J B)
      (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  apply Summable.of_norm
  refine hprod.of_nonneg_of_le (fun _ => norm_nonneg _) ?_
  intro pq
  by_cases hA : sources G (ofEdgeFun G pq.1) = A <;>
    by_cases hB : sources G (ofEdgeFun G pq.2) = B <;>
    by_cases hP : P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) <;>
    simp [hA, hB, hP, norm_mul] <;> positivity


theorem gatedSourcePairSum_partition (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P : Current V → Prop) [DecidablePred P]
    (f : Current V → Finset V) :
    gatedSourcePairSum G β J A B P =
      ∑ S : Finset V, gatedSourcePairSum G β J A B (fun m => f m = S ∧ P m) := by
  unfold gatedSourcePairSum
  rw [← Summable.tsum_finsetSum (s := (Finset.univ : Finset (Finset V)))
    (f := fun S (pq : (↥G.edgeFinset → ℕ) × (↥G.edgeFinset → ℕ)) =>
      (if sources G (ofEdgeFun G pq.1) = A then weight G β J (ofEdgeFun G pq.1) else 0) *
        (if sources G (ofEdgeFun G pq.2) = B then weight G β J (ofEdgeFun G pq.2) else 0) *
        (if f (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) = S ∧
            P (ofEdgeFun G (fun e => pq.1 e + pq.2 e)) then 1 else 0))
    (fun S _ => summable_gatedSourcePairSummand G β J A B
      (fun m => f m = S ∧ P m))]
  apply tsum_congr
  intro pq
  let m := ofEdgeFun G (fun e => pq.1 e + pq.2 e)
  by_cases hA : sources G (ofEdgeFun G pq.1) = A <;>
    by_cases hB : sources G (ofEdgeFun G pq.2) = B <;>
    by_cases hP : P m <;> simp [m, hA, hB, hP]


theorem gatedSourcePairSum_congr_sources (β : ℝ) (J : Sym2 V → ℝ)
    (A B : Finset V) (P Q : Current V → Prop) [DecidablePred P] [DecidablePred Q]
    (h : ∀ p q : ↥G.edgeFinset → ℕ,
      sources G (ofEdgeFun G p) = A → sources G (ofEdgeFun G q) = B →
        (P (ofEdgeFun G (fun e => p e + q e)) ↔
          Q (ofEdgeFun G (fun e => p e + q e)))) :
    gatedSourcePairSum G β J A B P = gatedSourcePairSum G β J A B Q := by
  unfold gatedSourcePairSum
  apply tsum_congr
  rintro ⟨p, q⟩
  change
    ((if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0) *
        (if P (ofEdgeFun G (fun e => p e + q e)) then 1 else 0)) =
      ((if sources G (ofEdgeFun G p) = A then weight G β J (ofEdgeFun G p) else 0) *
        (if sources G (ofEdgeFun G q) = B then weight G β J (ofEdgeFun G q) else 0) *
        (if Q (ofEdgeFun G (fun e => p e + q e)) then 1 else 0))
  by_cases hp : sources G (ofEdgeFun G p) = A <;>
    by_cases hq : sources G (ofEdgeFun G q) = B
  · rw [if_pos hp, if_pos hq]
    by_cases hP : P (ofEdgeFun G (fun e => p e + q e))
    · rw [if_pos hP, if_pos ((h p q hp hq).mp hP)]
    · rw [if_neg hP, if_neg (fun hQ => hP ((h p q hp hq).mpr hQ))]
  · simp [hp, hq]
  · simp [hp]
  · simp [hp]


theorem currentConnected_of_sources_pair (m : ↥G.edgeFinset → ℕ) {u v : V}
    (huv : u ≠ v) (hsrc : sources G (ofEdgeFun G m) = {u, v}) :
    CurrentConnected G (ofEdgeFun G m) u v := by
  have hnd : ∀ e ∈ G.edgeFinset, ¬ e.IsDiag := by
    intro e he
    exact G.not_isDiag_of_mem_edgeFinset he
  have hodd := Ising.connOdd_of_sources G.edgeFinset (ofEdgeFun G m) hnd huv (by
    simpa only using hsrc)
  have hpos := Ising.connOdd_imp_connPos G.edgeFinset (ofEdgeFun G m) hodd
  change Relation.ReflTransGen
    (Ising.adjP (Ising.posEdges G.edgeFinset (ofEdgeFun G m))) u v at hpos
  unfold CurrentConnected
  refine Relation.ReflTransGen.rec
    (motive := fun z _ => (currentSubgraph G (ofEdgeFun G m)).Reachable u z)
    (SimpleGraph.Reachable.refl u) ?_ hpos
  intro a b hab hstep ih
  apply SimpleGraph.Reachable.trans ih
  apply Adj.reachable
  obtain ⟨e, he, ha, hb, hne⟩ := hstep
  rw [Ising.posEdges, Finset.mem_filter, SimpleGraph.mem_edgeFinset] at he
  have heq : e = s(a, b) := (Sym2.mem_and_mem_iff hne).mp ⟨ha, hb⟩
  subst heq
  exact ⟨he.1, he.2⟩


theorem current_disconnect_dichotomy (m : ↥G.edgeFinset → ℕ)
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (hsrc : sources G (ofEdgeFun G m) = {o, x, y, g})
    (hng : ¬ CurrentConnected G (ofEdgeFun G m) o g) :
    (CurrentConnected G (ofEdgeFun G m) o x ∧
        CurrentConnected G (ofEdgeFun G m) y g) ∨
      (CurrentConnected G (ofEdgeFun G m) o y ∧
        CurrentConnected G (ofEdgeFun G m) x g) := by
  let U : Finset (FluxEdgeCopy.Copy G m) := Finset.univ
  have hsrcU : RandomCurrent.sources (FluxEdgeCopy.endsM G m) U = {o, x, y, g} := by
    rw [FluxEdgeCopy.sources_eq, FluxEdgeCopy.profileFlux_univ]
    exact hsrc
  have hngU : ¬ RandomCurrent.connK (FluxEdgeCopy.endsM G m) U o g := by
    simpa only [U, FluxEdgeCopy.connK_univ_iff] using hng
  have hd := RandomCurrent.disconnect_dichotomy (FluxEdgeCopy.endsM G m) U
    (fun i _ => FluxEdgeCopy.endsM_not_isDiag G m i)
    hox hoy hog hxy hxg hyg hsrcU hngU
  simpa only [U, FluxEdgeCopy.connK_univ_iff] using hd


theorem deltaSource_comm {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    (({o, g} : Finset V) ∆ {x, y}) = ({y, g} : Finset V) ∆ {o, x} := by
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  by_cases hzo : z = o <;> by_cases hzx : z = x <;>
    by_cases hzy : z = y <;> by_cases hzg : z = g <;> simp_all [eq_comm]


theorem deltaSource_eq_four {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g) :
    (({o, g} : Finset V) ∆ {x, y}) = {o, x, y, g} := by
  ext z
  simp only [Finset.mem_symmDiff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · tauto
  · intro hz
    rcases hz with rfl | rfl | rfl | rfl <;> simp_all [eq_comm]


theorem deltaEvent_notConnComp_iff
    {o x y g : V}
    (hox : o ≠ x) (hoy : o ≠ y) (hog : o ≠ g)
    (hxy : x ≠ y) (hxg : x ≠ g) (hyg : y ≠ g)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = ({o, g} : Finset V) ∆ {x, y})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o x ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x, y, g} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    rw [deltaSource_eq_four hox hoy hog hxy hxg hyg]
    ext z
    simp [Finset.mem_symmDiff]
  constructor
  · rintro ⟨hS, hoxc, hygC, hnog⟩
    have hoS : o ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m o)
    have hxS : x ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hoxc
    have hgS : g ∈ S := by
      rw [← hS, mem_notConnComp]
      exact hnog
    have hyS : y ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hoyc
      exact hnog (CurrentConnected.trans G hoyc hygC)
    exact ⟨⟨hyS, hgS, hoS, hxS⟩, hS⟩
  · rintro ⟨⟨hyS, hgS, hoS, hxS⟩, hS⟩
    have hny : ¬ CurrentConnected G m o y := by
      rw [← mem_notConnComp, hS]
      exact hyS
    have hng : ¬ CurrentConnected G m o g := by
      rw [← mem_notConnComp, hS]
      exact hgS
    rcases current_disconnect_dichotomy G (fun e => p e + q e)
      hox hoy hog hxy hxg hyg hsrc hng with hcase | hcase
    · exact ⟨hS, hcase.1, hcase.2, hng⟩
    · exact absurd hcase.1 hny


theorem middleEvent_notConnComp_iff {o x y g : V} (hox : o ≠ x)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = {o, x})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (o ∈ S ∧ x ∈ S ∧ y ∉ S ∧ g ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) g = S := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext z
    simp [Finset.mem_symmDiff]
  have hoxC : CurrentConnected G m o x :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hox hsrc
  constructor
  · rintro ⟨hS, hygC, hnog⟩
    have hgS : g ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m g)
    have hyS : y ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hygC.symm
    have hoS : o ∈ S := by
      rw [← hS, mem_notConnComp]
      exact fun hgo => hnog hgo.symm
    have hxS : x ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hgx
      exact hnog (CurrentConnected.trans G hoxC hgx.symm)
    exact ⟨⟨hoS, hxS, hyS, hgS⟩, hS⟩
  · rintro ⟨⟨hoS, hxS, hyS, hgS⟩, hS⟩
    have hygC : CurrentConnected G m y g := by
      have : ¬ y ∈ notConnComp G m g := by rw [hS]; exact hyS
      rw [mem_notConnComp] at this
      exact (not_not.mp this).symm
    have hnog : ¬ CurrentConnected G m o g := by
      have : o ∈ notConnComp G m g := by rw [hS]; exact hoS
      rw [mem_notConnComp] at this
      exact fun hogC => this hogC.symm
    exact ⟨hS, hygC, hnog⟩


theorem middleEvent_notConnCompO_iff {o x y g : V} (hox : o ≠ x)
    (S : Finset V) (p q : ↥G.edgeFinset → ℕ)
    (hp : sources G (ofEdgeFun G p) = {o, x})
    (hq : sources G (ofEdgeFun G q) = ∅) :
    (notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g ∧
        ¬ CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) o g) ↔
      (y ∈ S ∧ g ∈ S ∧ o ∉ S ∧ x ∉ S) ∧
        notConnComp G (ofEdgeFun G (fun e => p e + q e)) o = S ∧
        CurrentConnected G (ofEdgeFun G (fun e => p e + q e)) y g := by
  let m := ofEdgeFun G (fun e => p e + q e)
  have hsrc : sources G m = {o, x} := by
    dsimp [m]
    rw [← ofEdgeFun_add G p q, sources_add, hp, hq]
    ext z
    simp [Finset.mem_symmDiff]
  have hoxC : CurrentConnected G m o x :=
    currentConnected_of_sources_pair G (fun e => p e + q e) hox hsrc
  constructor
  · rintro ⟨hS, hygC, hnog⟩
    have hoS : o ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr (CurrentConnected.refl G m o)
    have hxS : x ∉ S := by
      rw [← hS, mem_notConnComp]
      exact not_not.mpr hoxC
    have hgS : g ∈ S := by
      rw [← hS, mem_notConnComp]
      exact hnog
    have hyS : y ∈ S := by
      rw [← hS, mem_notConnComp]
      intro hoyC
      exact hnog (CurrentConnected.trans G hoyC hygC)
    exact ⟨⟨hyS, hgS, hoS, hxS⟩, hS, hygC⟩
  · rintro ⟨⟨hyS, hgS, hoS, hxS⟩, hS, hygC⟩
    have hnog : ¬ CurrentConnected G m o g := by
      rw [← mem_notConnComp, hS]
      exact hgS
    exact ⟨hS, hygC, hnog⟩


end Sharpness
end StatMech
