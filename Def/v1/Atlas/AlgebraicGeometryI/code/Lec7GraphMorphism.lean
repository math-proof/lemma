/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec7GraphMorphism.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Data.Set.Function
import Mathlib.Tactic


/-- The graph of a function `f : X → Y` as the subset of `X × Y` of
pairs `(x, f x)` (Lec 7, Def 18). -/
def graphOfMorphism {X Y : Type*} (f : X → Y) : Set (X × Y) :=
  {p | p.2 = f p.1}

