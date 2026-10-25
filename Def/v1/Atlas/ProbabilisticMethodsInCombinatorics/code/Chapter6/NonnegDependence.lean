/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProbabilisticMethodsInCombinatorics/code/Chapter6/NonnegDependence.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Card
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Instance.v1.Atlas.ProbabilisticMethodsInCombinatorics.code.Chapter6.NonnegDependence
open Finset Function


namespace NonnegDependence

variable {X Y : Type*} [DecidableEq X] [DecidableEq Y] [Fintype X] [Fintype Y]

/-- The set of left endpoints covered by the matching $F$. -/
def Matching.leftVerts (F : Matching X Y) : Finset X := F.edges.image Prod.fst

/-- The set of right endpoints covered by the matching $F$. -/
def Matching.rightVerts (F : Matching X Y) : Finset Y := F.edges.image Prod.snd

/-- The injection $f : X \hookrightarrow Y$ extends the matching $F$ if $f(x) = y$ for every edge $(x, y) \in F$. -/
def extendsMatching (f : X ↪ Y) (F : Matching X Y) : Prop :=
  ∀ e ∈ F.edges, f e.1 = e.2

end NonnegDependence
