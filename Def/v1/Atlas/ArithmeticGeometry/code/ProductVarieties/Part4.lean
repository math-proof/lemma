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
import Theorem.v1.Atlas.ArithmeticGeometry.code.ProductVarieties.Part2
variable (k : Type*) [Field k]


/-- The combined polynomial set: union of the embeddings of homogeneous polynomial sets from
$\mathbb{P}^m$ and $\mathbb{P}^n$ into the bigger polynomial ring. -/
def combinedHomogPolySet {k : Type*} [Field k] (m n : ℕ)
    (S_X : Set (HomogPoly k m))
    (S_Y : Set (HomogPoly k n)) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  embedHomogSetLeft m n (HomogPoly.poly '' S_X) ∪
  embedHomogSetRight m n (HomogPoly.poly '' S_Y)

