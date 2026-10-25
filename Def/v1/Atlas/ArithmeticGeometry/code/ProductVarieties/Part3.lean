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
import Structure.v1.Atlas.ArithmeticGeometry.code.ProductVarieties
variable (k : Type*) [Field k]


/-- Embedding $\overline{k}[x_0, \ldots, x_m] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the first $m + 1$ variables. -/
noncomputable def embedHomogPolyLeft {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (m + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.castAdd (n + 1))

/-- Embedding $\overline{k}[y_0, \ldots, y_n] \hookrightarrow$ the bigger polynomial ring in
$m + 1 + (n + 1)$ variables, on the last $n + 1$ variables. -/
noncomputable def embedHomogPolyRight {k : Type*} [Field k] (m n : ℕ) :
    MvPolynomial (Fin (n + 1)) (AlgebraicClosure k) →ₐ[AlgebraicClosure k]
    MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k) :=
  MvPolynomial.rename (Fin.natAdd (m + 1))

/-- Image of a set of homogeneous polynomials under `embedHomogPolyLeft`. -/
def embedHomogSetLeft {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (m + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyLeft m n) '' S

/-- Image of a set of homogeneous polynomials under `embedHomogPolyRight`. -/
def embedHomogSetRight {k : Type*} [Field k] (m n : ℕ)
    (S : Set (MvPolynomial (Fin (n + 1)) (AlgebraicClosure k))) :
    Set (MvPolynomial (Fin (m + 1 + (n + 1))) (AlgebraicClosure k)) :=
  (embedHomogPolyRight m n) '' S

