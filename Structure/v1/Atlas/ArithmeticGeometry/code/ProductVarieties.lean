/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/ProductVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part9
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Varieties
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.Morphisms
import Def.v1.Atlas.ArithmeticGeometry.code.Morphisms.Part6
import Mathlib.Algebra.MvPolynomial.Rename
import Mathlib.Topology.NoetherianSpace
import Mathlib.RingTheory.MvPolynomial.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part2
variable (k : Type*) [Field k]


/-- A *bihomogeneous polynomial* of bi-degree $(d_X, d_Y)$: a polynomial in
$m + 1 + (n + 1)$ variables which is homogeneous of degree $d_X$ in the first $m + 1$
variables and homogeneous of degree $d_Y$ in the last $n + 1$ variables. -/
structure BihomogPoly (k : Type*) [Field k] (m n : ℕ) where
  poly : MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)
  degX : ℕ
  degY : ℕ
  homogX : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then c * v i else v i) poly =
    c ^ degX * eval v poly
  homogY : ∀ (c : AlgebraicClosure k) (v : Fin (m + 1 + (n + 1)) → AlgebraicClosure k),
    eval (fun i => if i.val < m + 1 then v i else c * v i) poly =
    c ^ degY * eval v poly

