/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePrimitive.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential.Part5
import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusPhaseAssembly
open scoped BigOperators


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularTorusEvenHomology_eq_zero_of_surfaceHomology
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hhom : surfaceSubgraphHomology (triangularTorusSurfaceEdgeClass L) F = 0) :
    triangularTorusEvenHomology L F = 0 := by
  have heq := triangularTorus_surfaceSubgraphHomology_eq L F
  rw [hhom] at heq
  apply Prod.ext
  · simpa using congrFun (congrArg Prod.fst heq.symm) 0
  · simpa using congrFun (congrArg Prod.snd heq.symm) 0


theorem triangularTorus_dartEdge_mem_cycle_iff
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall (k : Fin p.darts.length) (a : Fin 6),
      (triangularTorusDartEquiv L
          ((triangularTorusCycleNativeDart L p k).1, a)).edge ∈
          p.edges.toFinset ↔
        ((triangularTorusCycleNativeDart L p k).1, a) =
            triangularTorusCycleNativeDart L p k ∨
          ((triangularTorusCycleNativeDart L p k).1, a) =
            triangularTorusDartReverse L
              (triangularTorusCycleNativeDart L p (k - 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k a
  let q : triangularTorusDart L :=
    ((triangularTorusCycleNativeDart L p k).1, a)
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  rw [triangularTorusCycle_edges_toFinset_eq_image L p]
  constructor
  · rw [Finset.mem_image]
    rintro ⟨j, -, hedge⟩
    rcases (SimpleGraph.dart_edge_eq_iff
      (triangularTorusDartEquiv L q)
      (kwGraphCycleDartLoop p j)).mp hedge.symm with hsame | hreverse
    · left
      change q = d k
      have hnative : q = d j := by
        apply (triangularTorusDartEquiv L).injective
        calc
          triangularTorusDartEquiv L q = kwGraphCycleDartLoop p j := hsame
          _ = triangularTorusDartEquiv L (d j) := by
            symm
            exact triangularTorusCycleNativeDart_equiv L p j
      have hjk : j = k := by
        apply triangularTorusCycleNativeSite_injective L p hp
        change (d j).1 = (d k).1
        rw [← hnative]
      simpa [q, d, hjk] using hnative
    · right
      change q = triangularTorusDartReverse L (d (k - 1))
      have hnative : q = triangularTorusDartReverse L (d j) := by
        apply (triangularTorusDartEquiv L).injective
        rw [triangularTorusDartEquiv_reverse,
          triangularTorusCycleNativeDart_equiv]
        exact hreverse
      have hjk : j + 1 = k := by
        apply triangularTorusCycleNativeSite_injective L p hp
        change (d (j + 1)).1 = (d k).1
        rw [triangularTorusCycleNativeDart_fst L p (j + 1),
          triangularTorusCycleNativeDart_fst L p k]
        calc
          (kwGraphCycleDartLoop p (j + 1)).fst =
              (kwGraphCycleDartLoop p j).snd :=
            (kwGraphCycleDartLoop_valid p hp j).symm
          _ = (triangularTorusDartEquiv L q).fst := by
            exact congrArg
              (fun z : (triangularTorusGraph L).Dart ↦ z.fst) hreverse.symm
          _ = (kwGraphCycleDartLoop p k).fst := by
            change q.1 = (kwGraphCycleDartLoop p k).fst
            exact triangularTorusCycleNativeDart_fst L p k
      have hj : j = k - 1 := by
        calc
          j = (j + 1) - 1 := by abel
          _ = k - 1 := by rw [hjk]
      simpa [q, d, hj] using hnative
  · rintro (hsame | hreverse)
    · refine Finset.mem_image.mpr ⟨k, Finset.mem_univ _, ?_⟩
      rw [← triangularTorusCycleNativeDart_equiv L p k]
      exact (congrArg
        (fun z : triangularTorusDart L ↦ (triangularTorusDartEquiv L z).edge)
        hsame).symm
    · refine Finset.mem_image.mpr ⟨k - 1, Finset.mem_univ _, ?_⟩
      rw [← triangularTorusCycleNativeDart_equiv L p (k - 1)]
      calc
        (triangularTorusDartEquiv L
            (triangularTorusCycleNativeDart L p (k - 1))).edge =
            (triangularTorusDartEquiv L
              (triangularTorusDartReverse L
                (triangularTorusCycleNativeDart L p (k - 1)))).edge := by
          rw [triangularTorusDartEquiv_reverse,
            SimpleGraph.Dart.edge_symm]
        _ = (triangularTorusDartEquiv L q).edge := by
          exact congrArg
            (fun z : triangularTorusDart L ↦
              (triangularTorusDartEquiv L z).edge) hreverse.symm

theorem triangularZeroHomology_boundaryCoeff_cast
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L) :
    (triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d : ZMod 2) =
      (ons_edgeBit F (triangularTorusDartEquiv L d).edge : ZMod 2) := by
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a <;>
    simp [triangularFaceBoundaryCoeff, Int.cast_neg, CharTwo.neg_eq,
      triangularZeroHomology_eastCoeff_cast L F hF hhom,
      triangularZeroHomology_northCoeff_cast L F hF hhom,
      triangularZeroHomology_diagonalCoeff_cast,
      triangularTorusEastEdge, triangularTorusNorthEdge,
      triangularTorusNortheastEdge, triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart, triangularTorusDirectionStep,
      SimpleGraph.Dart.edge, Sym2.eq_swap]

theorem triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L)
    (hnot : (triangularTorusDartEquiv L d).edge ∉ F) :
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d = 0 := by
  have hcast :
      (triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L F)
          (triangularZeroHomologyUpperPotential L F) d : ZMod 2) = 0 := by
    rw [triangularZeroHomology_boundaryCoeff_cast L F hF hhom]
    rw [ons_edgeBit, if_neg hnot]
    rfl
  rcases d with ⟨⟨x, y⟩, a⟩
  fin_cases a
  · change -triangularFaceEastCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x - 1, y) = 0
    rw [neg_eq_zero]
    apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceEastCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast
  · change -triangularFaceNorthCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x, y - 1) = 0
    rw [neg_eq_zero]
    apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceNorthCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast
  · change -triangularFaceDiagonalCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) (x - 1, y - 1) = 0
    rw [neg_eq_zero]
    apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff, Int.cast_neg] using hcast
  · apply triangularFaceDiagonalCoeff_eq_zero_of_cast_eq_zero
    simpa [triangularFaceBoundaryCoeff] using hcast

theorem triangularZeroHomology_boundaryCoeff_ne_zero_of_mem
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (hhom : triangularTorusEvenHomology L F = 0)
    (d : triangularTorusDart L)
    (hmem : (triangularTorusDartEquiv L d).edge ∈ F) :
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L F)
        (triangularZeroHomologyUpperPotential L F) d ≠ 0 := by
  intro hz
  have hcast := triangularZeroHomology_boundaryCoeff_cast L F hF hhom d
  rw [hz] at hcast
  rw [ons_edgeBit, if_pos hmem] at hcast
  exact zero_ne_one hcast

theorem finSix_sum_eq_two
    (f : Fin 6 → Int) (a b : Fin 6) (hab : a ≠ b)
    (hzero : ∀ c, c ≠ a → c ≠ b → f c = 0) :
    (∑ c, f c) = f a + f b := by
  have hb : b ∈ (Finset.univ : Finset (Fin 6)).erase a := by
    simp [hab.symm]
  calc
    (∑ c, f c) = f a + ∑ c ∈ (Finset.univ : Finset (Fin 6)).erase a, f c := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ a)]
      abel
    _ = f a + (f b + ∑ c ∈
        ((Finset.univ : Finset (Fin 6)).erase a).erase b, f c) := by
      rw [← Finset.sum_erase_add _ _ hb]
      abel
    _ = f a + f b := by
      have hrest :
          (∑ c ∈ ((Finset.univ : Finset (Fin 6)).erase a).erase b,
            f c) = 0 := by
        apply Finset.sum_eq_zero
        intro c hc
        rw [Finset.mem_erase] at hc
        exact hzero c (Finset.mem_erase.mp hc.2).1 hc.1
      rw [hrest, add_zero]

theorem triangularZeroHomology_cycleBoundaryCoeff_eq_prev
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p k) =
        triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p (k - 1)) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  intro k
  let F := p.edges.toFinset
  let lower := triangularZeroHomologyLowerPotential L F
  let upper := triangularZeroHomologyUpperPotential L F
  let d : Fin p.darts.length → triangularTorusDart L :=
    triangularTorusCycleNativeDart L p
  let a : Fin 6 := (d k).2
  let b : Fin 6 := triangularTorusDirectionReverse (d (k - 1)).2
  have hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L) := by
    exact ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hab : a ≠ b := by
    have hnb := triangularTorus_cycleDirection_nonbacktracking L p hp (k - 1)
    simpa [a, b, d, triangularTorusCycleNativeDart_snd] using hnb
  have hincoming : ((d k).1, b) =
      triangularTorusDartReverse L (d (k - 1)) := by
    apply Prod.ext
    · change (d k).1 =
        (d (k - 1)).1 - triangularTorusDirectionStep L (d (k - 1)).2
      have hs := triangularTorusCycleNativeSite_succ L p hp (k - 1)
      rw [show k - 1 + 1 = k by abel,
        triangularIntReduce_step] at hs
      simpa [d, sub_eq_add_neg] using hs
    · rfl
  let f : Fin 6 → Int := fun c =>
    triangularFaceBoundaryCoeff lower upper ((d k).1, c)
  have hzero : ∀ c, c ≠ a → c ≠ b → f c = 0 := by
    intro c hca hcb
    have hnot : (triangularTorusDartEquiv L ((d k).1, c)).edge ∉ F := by
      intro hmem
      have hor := (triangularTorus_dartEdge_mem_cycle_iff L p hp k c).mp hmem
      rcases hor with hout | hin
      · apply hca
        exact congrArg Prod.snd hout
      · apply hcb
        exact congrArg Prod.snd (hin.trans hincoming.symm)
    exact triangularZeroHomology_boundaryCoeff_eq_zero_of_not_mem
      L F hF hhom ((d k).1, c) hnot
  have hsum : (∑ c, f c) = f a + f b :=
    finSix_sum_eq_two f a b hab hzero
  have hdiv := triangularFaceBoundaryCoeff_divergence lower upper (d k).1
  change (∑ c, f c) = 0 at hdiv
  rw [hsum] at hdiv
  have hfa : f a = triangularFaceBoundaryCoeff lower upper (d k) := by
    rfl
  have hfb : f b =
      -triangularFaceBoundaryCoeff lower upper (d (k - 1)) := by
    change triangularFaceBoundaryCoeff lower upper ((d k).1, b) = _
    rw [show ((d k).1, b) = triangularTorusDartReverse L (d (k - 1))
      from hincoming]
    exact triangularFaceBoundaryCoeff_reverse lower upper (d (k - 1))
  rw [hfa, hfb] at hdiv
  change triangularFaceBoundaryCoeff lower upper (d k) =
    triangularFaceBoundaryCoeff lower upper (d (k - 1))
  omega

theorem triangularZeroHomology_cycleBoundaryCoeff_eq_root
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    forall k : Fin p.darts.length,
      triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p k) =
        triangularFaceBoundaryCoeff
          (triangularZeroHomologyLowerPotential L p.edges.toFinset)
          (triangularZeroHomologyUpperPotential L p.edges.toFinset)
          (triangularTorusCycleNativeDart L p 0) := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  exact ons_fin_pred_invariant
    (fun k => triangularFaceBoundaryCoeff
      (triangularZeroHomologyLowerPotential L p.edges.toFinset)
      (triangularZeroHomologyUpperPotential L p.edges.toFinset)
      (triangularTorusCycleNativeDart L p k))
    (triangularZeroHomology_cycleBoundaryCoeff_eq_prev L p hp hhom)

theorem triangularZeroHomology_cycleBoundaryCoeff_root_ne_zero
    (L : Nat) [Fact (2 < L)] {root : ZMod L × ZMod L}
    (p : (triangularTorusGraph L).Walk root root) (hp : p.IsCycle)
    (hhom : triangularTorusEvenHomology L p.edges.toFinset = 0) :
    letI : NeZero p.darts.length :=
      ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
        (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
    triangularFaceBoundaryCoeff
        (triangularZeroHomologyLowerPotential L p.edges.toFinset)
        (triangularZeroHomologyUpperPotential L p.edges.toFinset)
        (triangularTorusCycleNativeDart L p 0) ≠ 0 := by
  letI : NeZero p.darts.length :=
    ⟨Nat.ne_of_gt (List.length_pos_of_ne_nil
      (SimpleGraph.Walk.darts_eq_nil.not.mpr hp.not_nil))⟩
  have hF : p.edges.toFinset ∈
      StatMech.Ising.evenSubgraphs (triangularTorusGraph L) :=
    ons_cycle_edges_evenSubgraph (triangularTorusGraph L) p hp
  have hedge :
      (triangularTorusDartEquiv L
        (triangularTorusCycleNativeDart L p 0)).edge ∈ p.edges.toFinset := by
    rw [triangularTorusCycle_edges_toFinset_eq_image L p,
      Finset.mem_image]
    exact ⟨0, Finset.mem_univ _, by
      rw [triangularTorusCycleNativeDart_equiv]⟩
  exact triangularZeroHomology_boundaryCoeff_ne_zero_of_mem
    L p.edges.toFinset hF hhom _ hedge

end StatMech.FrontierA
