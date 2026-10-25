/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/kwd_parityconfig.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Def.StatisticalMechanics.Code.Walls.kwd_parityconfig
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech.Walls

section WalkParity

variable {V : Type*} [DecidableEq V] (G : SimpleGraph V) (δ : Finset (Sym2 V))


@[simp] theorem walkPar_nil {x : V} : walkPar G δ (.nil : G.Walk x x) = false := rfl

@[simp] theorem walkPar_cons {u v w : V} (h : G.Adj u v) (p : G.Walk v w) :
    walkPar G δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkPar G δ p) := rfl

variable {G δ}


theorem walkPar_append {x y z : V} (p : G.Walk x y) (q : G.Walk y z) :
    walkPar G δ (p.append q) = (walkPar G δ p).xor (walkPar G δ q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, ih]


theorem walkPar_reverse {x y : V} (p : G.Walk x y) :
    walkPar G δ p.reverse = walkPar G δ p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkPar_append, ih, walkPar_cons,
      show walkPar G δ (SimpleGraph.Walk.cons h p)
        = (decide (s(u, v) ∈ δ)).xor (walkPar G δ p) from rfl]
    have hedge : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [walkPar_nil, hedge, Bool.xor_false]
    cases walkPar G δ p <;> cases hb : decide (s(u, v) ∈ δ) <;> simp [Bool.xor_comm]


@[simp] theorem walkPar_singleton {x y : V} (h : G.Adj x y) :
    walkPar G δ (SimpleGraph.Walk.cons h (.nil : G.Walk y y)) = decide (s(x, y) ∈ δ) := by
  simp

end WalkParity
end StatMech.Walls
