/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/Varieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.AffineVarieties.Part5
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.AffineVarieties
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Def.v1.Atlas.ArithmeticGeometry.code.Varieties.Part8
variable (k : Type*) [Field k]


/-- A rational map with all denominators equal to $1$ reduces to a polynomial map. -/
lemma ratMapEval_eq_polyMapEval_of_denom_one {m n : ℕ}
    (polys : Fin n → MvPolynomial (Fin m) (AlgebraicClosure k))
    (P : AffineSpace_k k m) :
    ratMapEval k m n polys (fun _ => 1) P = polyMapEval k m n polys P := by
  ext j
  simp [ratMapEval, ratFunEval, polyMapEval, map_one, div_one]

/-- If all denominators are $1$, the domain of the rational map is all of $X$. -/
lemma ratMapDom_of_denom_one {m n : ℕ} (X : Set (AffineSpace_k k m)) :
    ratMapDom k m n X (fun _ => (1 : MvPolynomial (Fin m) (AlgebraicClosure k))) = X := by
  ext P
  simp [ratMapDom, map_one]

