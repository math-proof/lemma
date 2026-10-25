/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/ChamberComplex/CoxeterComplex.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.Buildings.code.ChamberComplex.Basic
import Mathlib.GroupTheory.Coxeter.Basic
variable {B : Type*} [DecidableEq B] [Fintype B]


namespace CoxeterComplex

omit [DecidableEq B] [Fintype B] in
/-- Two elements $w, w'$ of the Coxeter group $W$ are *chamber-adjacent* when $w \neq w'$ and
$w' = w \cdot s_i$ for some simple generator $s_i$. -/
def ChamberAdjacent (M : CoxeterMatrix B) (w w' : M.Group) : Prop :=
  w ≠ w' ∧ ∃ i : B, w' = w * M.toCoxeterSystem.simple i

omit [DecidableEq B] [Fintype B] in
/-- A list of group elements is a gallery in the Coxeter complex iff consecutive entries are
chamber-adjacent. -/
def IsGallery (M : CoxeterMatrix B) : List M.Group → Prop
  | [] => True
  | [_] => True
  | w :: w' :: rest => ChamberAdjacent M w w' ∧ IsGallery M (w' :: rest)

end CoxeterComplex
