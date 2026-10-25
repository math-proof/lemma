/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamFourColorBalancedCore.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Theorem.StatisticalMechanics.Code.Ising.GKS2.Part4
import Theorem.StatisticalMechanics.Code.Ising.AizenmanBarsky.Part5
import Theorem.StatisticalMechanics.Code.Ising.GHSThreePoint
import Theorem.StatisticalMechanics.Code.Ising.CorrelationRatio
import Theorem.StatisticalMechanics.Code.Ising.CurrentWeight.Part2
import Theorem.StatisticalMechanics.Code.Sharpness.GhostCurrentRep
import Theorem.StatisticalMechanics.Code.Sharpness.ClaimIsingFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.BackbonePropsFull.Part4
import Theorem.StatisticalMechanics.Code.Sharpness.Simon.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc10ghostfourpoint
import Theorem.StatisticalMechanics.Code.Walls.ghc_urselleqgap
import Theorem.StatisticalMechanics.Code.Walls.vbgtriangle.Part3
import Theorem.StatisticalMechanics.Code.Walls.gc7ghosteven
import Def.StatisticalMechanics.Code.FrontierA.GrahamFourColorBalancedCore.Part4
open scoped BigOperators symmDiff
open Finset


namespace StatMech

namespace GrahamGHS

open Ising

open Sharpness


namespace FourColor

variable {W ι : Type*} [Fintype W] [DecidableEq W] [Fintype ι] [DecidableEq ι]


theorem mem_edgeComponent_of_endpoint {ends : ι → Sym2 W} {K : Finset ι}
    {u : W} {i : ι} (hi : i ∈ K) (hu : u ∈ ends i) :
    i ∈ edgeComponent ends K u := by
  classical
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hi, ?_⟩
  intro x hx
  by_cases hux : u = x
  · subst x
    exact Relation.ReflTransGen.refl
  · exact Relation.ReflTransGen.single ⟨i, hi, hu, hx, hux⟩

theorem mem_edgeComponent_of_reachable_endpoint {ends : ι → Sym2 W} {K : Finset ι}
    {u x : W} {i : ι} (hux : Sharpness.RandomCurrent.connK ends K u x)
    (hi : i ∈ K) (hx : x ∈ ends i) : i ∈ edgeComponent ends K u := by
  classical
  rw [edgeComponent, Finset.mem_filter]
  refine ⟨hi, ?_⟩
  intro y hy
  by_cases hxy : x = y
  · simpa [hxy] using hux
  · exact hux.tail ⟨i, hi, hx, hy, hxy⟩


theorem degK_inter_edgeComponent_of_conn {ends : ι → Sym2 W} {T K : Finset ι}
    (hTK : T ⊆ K) {u x : W} (hux : Sharpness.RandomCurrent.connK ends K u x) :
    Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x =
      Sharpness.RandomCurrent.degK ends T x := by
  classical
  unfold Sharpness.RandomCurrent.degK
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_inter]
  constructor
  · exact fun h => ⟨h.1.1, h.2⟩
  · rintro ⟨hiT, hxi⟩
    exact ⟨⟨hiT, mem_edgeComponent_of_reachable_endpoint hux (hTK hiT) hxi⟩, hxi⟩


theorem degK_inter_edgeComponent_of_not_conn {ends : ι → Sym2 W} {T K : Finset ι}
    {u x : W} (hux : ¬ Sharpness.RandomCurrent.connK ends K u x) :
    Sharpness.RandomCurrent.degK ends (T ∩ edgeComponent ends K u) x = 0 := by
  classical
  unfold Sharpness.RandomCurrent.degK
  rw [Finset.card_eq_zero]
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_inter] at hi
  rw [edgeComponent, Finset.mem_filter] at hi
  exact hux (hi.1.2.2 x hi.2)


theorem sources_inter_edgeComponent {ends : ι → Sym2 W} {T K : Finset ι}
    (hTK : T ⊆ K) (u : W) :
    Sharpness.RandomCurrent.sources ends (T ∩ edgeComponent ends K u) =
      Sharpness.RandomCurrent.sources ends T ∩
        Sharpness.RandomCurrent.compOf ends K u := by
  ext x
  simp only [Sharpness.RandomCurrent.mem_sources, Finset.mem_inter,
    Sharpness.RandomCurrent.mem_compOf]
  by_cases hux : Sharpness.RandomCurrent.connK ends K u x
  · rw [degK_inter_edgeComponent_of_conn hTK hux]
    simp only [hux, and_true]
  · rw [degK_inter_edgeComponent_of_not_conn hux]
    simp [hux]

theorem sources_union_of_disjoint {ends : ι → Sym2 W} {S T : Finset ι}
    (hST : Disjoint S T) :
    Sharpness.RandomCurrent.sources ends (S ∪ T) =
      Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
  have hu : S ∪ T = S ∆ T := by
    ext i
    simp only [Finset.mem_union, Finset.mem_symmDiff]
    rw [Finset.disjoint_left] at hST
    aesop
  rw [hu, Sharpness.RandomCurrent.sources_symmDiff]

theorem sources_sdiff_of_subset {ends : ι → Sym2 W} {S T : Finset ι} (hTS : T ⊆ S) :
    Sharpness.RandomCurrent.sources ends (S \ T) =
      Sharpness.RandomCurrent.sources ends S ∆ Sharpness.RandomCurrent.sources ends T := by
  have heq : S \ T = S ∆ T := by
    ext i
    have hmem := @hTS i
    simp only [Finset.mem_sdiff, Finset.mem_symmDiff]
    aesop
  rw [heq, Sharpness.RandomCurrent.sources_symmDiff]

theorem sources_edgeComponent {ends : ι → Sym2 W} (K : Finset ι) (u : W) :
    Sharpness.RandomCurrent.sources ends (edgeComponent ends K u) =
      Sharpness.RandomCurrent.sources ends K ∩ Sharpness.RandomCurrent.compOf ends K u := by
  classical
  have hcap : K ∩ edgeComponent ends K u = edgeComponent ends K u := by
    ext i
    simp only [Finset.mem_inter]
    constructor
    · exact fun hi => hi.2
    · intro hi
      have hiK : i ∈ K := by
        rw [edgeComponent, Finset.mem_filter] at hi
        exact hi.1
      exact ⟨hiK, hi⟩
  rw [← hcap, sources_inter_edgeComponent Finset.Subset.rfl]

theorem not_connK_of_no_incident {ends : ι → Sym2 W} {K : Finset ι} {u v : W}
    (huv : u ≠ v) (hinc : ∀ i ∈ K, u ∉ ends i) :
    ¬ Sharpness.RandomCurrent.connK ends K u v := by
  intro huvconn
  have heq : ∀ x, Sharpness.RandomCurrent.connK ends K u x → x = u := by
    intro x hx
    induction hx with
    | refl => rfl
    | tail hab hstep ih =>
        rw [ih] at hstep
        rcases hstep with ⟨i, hi, hu, -, -⟩
        exact False.elim (hinc i hi hu)
  exact huv (heq v huvconn).symm


end FourColor
end GrahamGHS
end StatMech
