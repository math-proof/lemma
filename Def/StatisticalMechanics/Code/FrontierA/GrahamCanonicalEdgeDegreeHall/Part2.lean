/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.GrahamTightRootCutHallEquivalence
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part2
open Finset
open scoped symmDiff


namespace StatMech.FrontierA

variable {A B : Type*} [Fintype A] [Fintype B]


def BipartiteCollisionTokenEmbedding
    [DecidableEq A] [DecidableEq B]
    (r : A -> B -> Prop) [DecidableRel r]
    (S : Finset A) (N : Finset B) : Prop :=
  ∃ (leftBase : ↑S -> B) (rightBase : ↑N -> A),
    (∀ a, r a.1 (leftBase a)) ∧
      (∀ b, rightBase b ∈ S ∧ r (rightBase b) b.1) ∧
      Nonempty
        (bipartiteRightCollisionToken r S N rightBase ↪
          bipartiteLeftSurplusToken r S leftBase)


end StatMech.FrontierA
