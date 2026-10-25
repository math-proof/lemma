/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Def.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


noncomputable instance instFintypeBipartiteLeftSurplusToken
    [DecidableEq B] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (base : ↑S -> B) :
    Fintype (bipartiteLeftSurplusToken r S base) := by
  unfold bipartiteLeftSurplusToken
  infer_instance

noncomputable instance instFintypeBipartiteRightCollisionToken
    [DecidableEq A] (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) (base : ↑N -> A) :
    Fintype (bipartiteRightCollisionToken r S N base) := by
  unfold bipartiteRightCollisionToken
  infer_instance


end StatMech.FrontierA
