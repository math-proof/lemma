/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusFacePotential.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFaceBoundary
import Theorem.StatisticalMechanics.Code.Onsager.TorusPrimitiveWinding.Part3
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusFacePotential
open scoped BigOperators
open scoped symmDiff


namespace StatMech.FrontierA

open StatMech.Onsager

theorem triangularTorusPositiveDirection_injective :
    Function.Injective triangularTorusPositiveDirection := by
  intro a b h
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusPositiveDirection] at h ⊢

theorem triangularTorusPositiveEdge_eq_iff
    (L : Nat) [Fact (2 < L)]
    (p q : ZMod L × ZMod L) (a b : Fin 3) :
    (triangularTorusDartEquiv L
        (p, triangularTorusPositiveDirection a)).edge =
      (triangularTorusDartEquiv L
        (q, triangularTorusPositiveDirection b)).edge ↔
      p = q ∧ a = b := by
  constructor
  · intro hedge
    rcases (SimpleGraph.dart_edge_eq_iff
      (triangularTorusDartEquiv L
        (p, triangularTorusPositiveDirection a))
      (triangularTorusDartEquiv L
        (q, triangularTorusPositiveDirection b))).mp hedge with hsame | hrev
    · have hnative := (triangularTorusDartEquiv L).injective hsame
      exact ⟨congrArg Prod.fst hnative,
        triangularTorusPositiveDirection_injective
          (congrArg Prod.snd hnative)⟩
    · have hnative :
          (p, triangularTorusPositiveDirection a) =
            triangularTorusDartReverse L
              (q, triangularTorusPositiveDirection b) := by
        apply (triangularTorusDartEquiv L).injective
        rw [triangularTorusDartEquiv_reverse]
        exact hrev
      have hdir := congrArg Prod.snd hnative
      fin_cases a <;> fin_cases b <;>
        simp [triangularTorusPositiveDirection,
          triangularTorusDartReverse,
          triangularTorusDirectionReverse] at hdir
  · rintro ⟨rfl, rfl⟩
    rfl

theorem triangularTorusEastEdge_eq_ons
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularTorusEastEdge L p = ons_portEdge L (p, 0) := by
  rcases p with ⟨x, y⟩
  simp [triangularTorusEastEdge, triangularTorusDartEquiv_apply,
    triangularTorusDartToGraphDart, triangularTorusDirectionStep,
    ons_portEdge, ons_dirStep, SimpleGraph.Dart.edge]

theorem triangularTorusNorthEdge_eq_ons
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    triangularTorusNorthEdge L p = ons_portEdge L (p, 1) := by
  rcases p with ⟨x, y⟩
  simp [triangularTorusNorthEdge, triangularTorusDartEquiv_apply,
    triangularTorusDartToGraphDart, triangularTorusDirectionStep,
    ons_portEdge, ons_dirStep, SimpleGraph.Dart.edge]

theorem ons_eastPortEdge_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 0)) := by
  intro p q hpq
  rcases (ons_portEdge_eq_iff L (p, 0) (q, 0)).mp hpq.symm with h | h
  · exact (congrArg Prod.fst h).symm
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem ons_northPortEdge_injective
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (fun p : ZMod L × ZMod L => ons_portEdge L (p, 1)) := by
  intro p q hpq
  rcases (ons_portEdge_eq_iff L (p, 1) (q, 1)).mp hpq.symm with h | h
  · exact (congrArg Prod.fst h).symm
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem ons_eastPortEdge_ne_northPortEdge
    (L : Nat) [Fact (2 < L)] (p q : ZMod L × ZMod L) :
    ons_portEdge L (p, 0) ≠ ons_portEdge L (q, 1) := by
  intro hpq
  rcases (ons_portEdge_eq_iff L (p, 0) (q, 1)).mp hpq.symm with h | h
  · have hdir := congrArg Prod.snd h
    simp at hdir
  · have hdir := congrArg Prod.snd h
    simp [ons_dartRev] at hdir

theorem triangularTorusDirectionStep_injective_public
    (L : Nat) [Fact (2 < L)] :
    Function.Injective (triangularTorusDirectionStep L) := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have h2 : (2 : ZMod L) ≠ 0 := by
    rw [Ne, ← Nat.cast_ofNat, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hle := Nat.le_of_dvd (by norm_num) hdvd
    have := (Fact.out : 2 < L)
    omega
  have hm1 : (-1 : ZMod L) ≠ 0 := neg_ne_zero.mpr h1
  have hpm : (1 : ZMod L) ≠ -1 := by
    intro h
    apply h2
    linear_combination h
  have h01 : (0 : ZMod L) ≠ 1 := Ne.symm h1
  have hmp : (-1 : ZMod L) ≠ 1 := Ne.symm hpm
  intro a b hab
  fin_cases a <;> fin_cases b <;>
    simp [triangularTorusDirectionStep, h1, hm1, hpm, h01, hmp] at hab ⊢

theorem triangularTorus_neighborFinset_steps
    (L : Nat) [Fact (2 < L)] (p : ZMod L × ZMod L) :
    (triangularTorusGraph L).neighborFinset p =
      Finset.univ.image (fun a : Fin 6 =>
        p - triangularTorusDirectionStep L a) := by
  ext q
  simp only [SimpleGraph.mem_neighborFinset, Finset.mem_image,
    Finset.mem_univ, true_and]
  constructor
  · intro hadj
    change triangularTorusAdj L p q at hadj
    rcases hadj with
      (⟨hcoord, hstep | hstep⟩ | ⟨hcoord, hstep | hstep⟩) |
        (⟨hx, hy⟩ | ⟨hx, hy⟩)
    · refine ⟨2, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
    · refine ⟨3, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
    · refine ⟨0, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
    · refine ⟨1, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hstep]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hcoord]
    · refine ⟨4, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hx]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hy]
        ring
    · refine ⟨5, ?_⟩
      apply Prod.ext
      · simp [triangularTorusDirectionStep]
        rw [hx]
        ring
      · simp [triangularTorusDirectionStep]
        rw [hy]
        ring
  · rintro ⟨a, rfl⟩
    fin_cases a <;>
      simp [triangularTorusGraph, triangularTorusAdj, onsTorusAdj,
        triangularTorusDirectionStep] <;> ring

theorem sum_fin_six {A : Type*} [AddCommMonoid A]
    (f : Fin 6 → A) :
    (∑ i, f i) = f 0 + f 1 + f 2 + f 3 + f 4 + f 5 := by
  exact Fin.sum_univ_six f

set_option maxHeartbeats 800000 in


theorem triangularTorus_edgeBits_divergence_zero
    (L : Nat) [Fact (2 < L)]
    (F : Finset (Sym2 (ZMod L × ZMod L)))
    (hF : F ∈ StatMech.Ising.evenSubgraphs (triangularTorusGraph L))
    (p : ZMod L × ZMod L) :
    (ons_edgeBit F (triangularTorusEastEdge L p) : ZMod 2) +
      ons_edgeBit F (triangularTorusEastEdge L (p.1 - 1, p.2)) +
      ons_edgeBit F (triangularTorusNorthEdge L p) +
      ons_edgeBit F (triangularTorusNorthEdge L (p.1, p.2 - 1)) +
      ons_edgeBit F (triangularTorusNortheastEdge L p) +
      ons_edgeBit F
        (triangularTorusNortheastEdge L (p.1 - 1, p.2 - 1)) = 0 := by
  have hsum := ons_evenSubgraph_neighbor_sum_zero
    (triangularTorusGraph L) F hF p
  rw [triangularTorus_neighborFinset_steps L p] at hsum
  have hinj : Function.Injective (fun a : Fin 6 =>
      p - triangularTorusDirectionStep L a) := by
    intro a b hab
    apply triangularTorusDirectionStep_injective_public L
    apply Prod.ext
    · have h := congrArg Prod.fst hab
      dsimp at h ⊢
      linear_combination -h
    · have h := congrArg Prod.snd hab
      dsimp at h ⊢
      linear_combination -h
  have hreindex :
      (∑ w ∈ Finset.univ.image (fun a : Fin 6 =>
          p - triangularTorusDirectionStep L a),
          if s(p, w) ∈ F then (1 : ZMod 2) else 0) =
        ∑ a : Fin 6,
          if s(p, p - triangularTorusDirectionStep L a) ∈ F then
            (1 : ZMod 2) else 0 := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact hinj hab
  rw [hreindex] at hsum
  rw [sum_fin_six] at hsum
  have hpadd (x y : ZMod L) :
      p + (x, y) = (p.1 + x, p.2 + y) := by
    rcases p
    rfl
  simpa [ons_edgeBit, triangularTorusEastEdge,
    triangularTorusNorthEdge, triangularTorusNortheastEdge,
    triangularTorusDartEquiv_apply, triangularTorusDartToGraphDart,
    triangularTorusDirectionStep, SimpleGraph.Dart.edge,
    sub_eq_add_neg, hpadd, Sym2.eq_swap,
    add_assoc, add_left_comm, add_comm] using hsum

end StatMech.FrontierA
