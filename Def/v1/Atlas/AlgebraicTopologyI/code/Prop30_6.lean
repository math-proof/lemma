/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Prop30_6.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.BilinFormClassification
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.BilinFormClassification
open Matrix


namespace SymmetricBilinearForms

/-- **The standard normal form (matrix presentation) of Proposition 30.6.**
The Gram matrix of the block-diagonal form on `(ZMod 2)^{a+2b}` consisting
of `a` copies of the rank-one form `[1]` followed by `b` copies of the
hyperbolic plane `⎡⎣0 1 / 1 0⎤⎦`.  Indices `0,…,a-1` form the diagonal
block; indices `a, a+1, a+2, a+3, …` form pairs `(a+2k, a+2k+1)` each
giving a hyperbolic plane.  This is the matrix appearing on the right-hand
side of the classification theorem below. -/
def standardFormF2 (a b : ℕ) :
    Matrix (Fin (a + 2 * b)) (Fin (a + 2 * b)) (ZMod 2) :=
  fun i j =>
    let iv := i.val
    let jv := j.val
    if iv < a ∧ jv < a then
      if iv = jv then 1 else 0
    else if iv ≥ a ∧ jv ≥ a then
      let iv' := iv - a
      let jv' := jv - a
      if iv' / 2 = jv' / 2 then
        if iv' % 2 ≠ jv' % 2 then 1 else 0
      else 0
    else 0

end SymmetricBilinearForms
