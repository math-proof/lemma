/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/KramersWannierEvenToCut.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.KramersWannierGeneral.Part5
import Def.StatisticalMechanics.Code.Ising.KramersWannierEvenToCut
open scoped BigOperators
open Finset SimpleGraph


namespace StatMech

namespace Ising

section CutParity

variable {V : Type*} [DecidableEq V] (Gp : SimpleGraph V) (δ : Finset (Sym2 V))


@[simp] theorem walkParity_nil {x : V} : walkParity Gp δ (.nil : Gp.Walk x x) = false := rfl

@[simp] theorem walkParity_cons {u v w : V} (h : Gp.Adj u v) (p : Gp.Walk v w) :
    walkParity Gp δ (.cons h p) = (decide (s(u, v) ∈ δ)).xor (walkParity Gp δ p) := rfl

variable {Gp δ}


theorem walkParity_append {x y z : V} (p : Gp.Walk x y) (q : Gp.Walk y z) :
    walkParity Gp δ (p.append q) = (walkParity Gp δ p).xor (walkParity Gp δ q) := by
  induction p with
  | nil => simp
  | cons h p ih => simp [SimpleGraph.Walk.cons_append, ih]


theorem walkParity_reverse {x y : V} (p : Gp.Walk x y) :
    walkParity Gp δ p.reverse = walkParity Gp δ p := by
  induction p with
  | nil => simp
  | @cons u v w h p ih =>
    rw [SimpleGraph.Walk.reverse_cons, walkParity_append, ih, walkParity_cons,
      show walkParity Gp δ (SimpleGraph.Walk.cons h p)
        = (decide (s(u, v) ∈ δ)).xor (walkParity Gp δ p) from rfl]
    
    have hedge : s(v, u) = s(u, v) := Sym2.eq_swap
    rw [walkParity_nil, hedge, Bool.xor_false]
    cases walkParity Gp δ p <;> cases hb : decide (s(u, v) ∈ δ) <;> simp [Bool.xor_comm]


@[simp] theorem walkParity_singleton {x y : V} (h : Gp.Adj x y) :
    walkParity Gp δ (SimpleGraph.Walk.cons h (.nil : Gp.Walk y y)) = decide (s(x, y) ∈ δ) := by
  simp

end CutParity
end Ising
end StatMech
