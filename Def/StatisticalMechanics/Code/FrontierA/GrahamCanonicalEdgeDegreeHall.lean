/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


noncomputable def bipartiteLeftSurplusToken
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B) : Type _ :=
  Σ a : ↑S, ↑((Finset.univ.filter (r a.1)).erase (base a))


noncomputable def bipartiteRightCollisionToken
    [DecidableEq A] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) (base : ↑N -> A) : Type _ :=
  Σ b : ↑N, ↑((S.filter fun a => r a b.1).erase (base b))

end StatMech.FrontierA
