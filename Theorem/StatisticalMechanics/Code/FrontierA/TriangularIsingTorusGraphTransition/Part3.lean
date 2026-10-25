/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/TriangularIsingTorusGraphTransition.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusSectorContinuation
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
import Def.StatisticalMechanics.Code.FrontierA.TriangularIsingTorusGraphTransition.Part2


namespace StatMech.FrontierA

open SimpleGraph StatMech.Onsager

@[simp] theorem triangularTorusDartEquiv_apply
    (L : Nat) [Fact (2 < L)] (d : triangularTorusDart L) :
    triangularTorusDartEquiv L d = triangularTorusDartToGraphDart L d :=
  rfl

theorem squareTorusHorizontalEdge_mk_iff
    (L : Nat) (p q : ZMod L × ZMod L) :
    squareTorusHorizontalEdge L s(p, q) ↔
      p.2 = q.2 ∧ (p.1 = q.1 + 1 ∨ p.1 = q.1 - 1) := by
  constructor
  · rintro ⟨r, hr⟩
    change s(p, q) = s(r, (r.1 + 1, r.2)) at hr
    rw [Sym2.eq_iff] at hr
    rcases hr with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inr (by ring)⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  · rintro ⟨h2, h1 | h1⟩
    · refine ⟨q, ?_⟩
      change s(p, q) = s(q, (q.1 + 1, q.2))
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Prod.ext h1 h2, rfl⟩
    · refine ⟨p, ?_⟩
      change s(p, q) = s(p, (p.1 + 1, p.2))
      rw [Sym2.eq_iff]
      apply Or.inl
      refine ⟨rfl, Prod.ext ?_ h2.symm⟩
      simpa using (congrArg (fun z : ZMod L => z + 1) h1).symm

theorem triangularTorusVerticalEdge_mk_iff
    (L : Nat) (p q : ZMod L × ZMod L) :
    triangularTorusVerticalEdge L s(p, q) ↔
      p.1 = q.1 ∧ (p.2 = q.2 + 1 ∨ p.2 = q.2 - 1) := by
  constructor
  · rintro ⟨r, hr⟩
    change s(p, q) = s(r, (r.1, r.2 + 1)) at hr
    rw [Sym2.eq_iff] at hr
    rcases hr with h | h
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inr (by ring)⟩
    · rcases h with ⟨rfl, rfl⟩
      exact ⟨rfl, Or.inl rfl⟩
  · rintro ⟨h1, h2 | h2⟩
    · refine ⟨q, ?_⟩
      change s(p, q) = s(q, (q.1, q.2 + 1))
      rw [Sym2.eq_iff]
      exact Or.inr ⟨Prod.ext h1 h2, rfl⟩
    · refine ⟨p, ?_⟩
      change s(p, q) = s(p, (p.1, p.2 + 1))
      rw [Sym2.eq_iff]
      apply Or.inl
      refine ⟨rfl, Prod.ext h1.symm ?_⟩
      simpa using (congrArg (fun z : ZMod L => z + 1) h2).symm


theorem triangularTorusEdgeWeight_dart
    (L : Nat) [Fact (2 < L)] (t1 t2 t3 : Complex)
    (d : triangularTorusDart L) :
    triangularTorusEdgeWeight L t1 t2 t3
        (triangularTorusDartEquiv L d).edge =
      triangularTorusDirectionWeight t1 t2 t3 d.2 := by
  have h1 : (1 : ZMod L) ≠ 0 := by
    letI : Fact (1 < L) := ⟨by have := (Fact.out : 2 < L); omega⟩
    exact one_ne_zero
  have hshift (z : ZMod L) : z ≠ -1 + z := by
    intro h
    apply h1
    linear_combination h
  rcases d with ⟨p, a⟩
  fin_cases a
  all_goals simp [triangularTorusDartEquiv_apply,
      triangularTorusDartToGraphDart,
      SimpleGraph.Dart.edge, triangularTorusEdgeWeight,
      triangularTorusDirectionWeight, triangularTorusDirectionStep,
      squareTorusHorizontalEdge_mk_iff,
      triangularTorusVerticalEdge_mk_iff, h1] <;> try ring
  · intro hp
    exact (hshift p.2 hp).elim
  · rw [if_neg (hshift p.2), if_neg (hshift p.1)]


end StatMech.FrontierA
