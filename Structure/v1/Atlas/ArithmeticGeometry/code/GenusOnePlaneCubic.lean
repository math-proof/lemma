/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/GenusOnePlaneCubic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib


public noncomputable section

open MvPolynomial AlgebraicGeometry CategoryTheory

/-- A smooth projective curve over a field $k$ packaged as: an underlying scheme (with proofs of
integrality, Krull dimension one, nonemptiness), a structure morphism to $\mathrm{Spec}\,k$, and a
(declared) genus value. The smoothness is left implicit. -/
structure SmoothProjectiveCurveOverField (k : Type*) [Field k] where
  toScheme : Scheme
  isIntegral : AlgebraicGeometry.IsIntegral toScheme
  krullDim_eq : topologicalKrullDim toScheme = 1
  nonempty : Nonempty toScheme
  structureMorphism : toScheme ⟶ Spec (CommRingCat.of k)
  genusVal : ℕ

namespace SmoothProjectiveCurveOverField

/-- The genus of a smooth projective curve, given by the structural field `genusVal`. -/
def genus {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : ℕ := C.genusVal

/-- A smooth projective curve has a rational point if its structure morphism admits a section, i.e.
a morphism $\mathrm{Spec}\,k \to C$ that composes to the identity. -/
def HasRationalPoint {k : Type*} [Field k]
    (C : SmoothProjectiveCurveOverField k) : Prop :=
  ∃ s : Spec (CommRingCat.of k) ⟶ C.toScheme, s ≫ C.structureMorphism = 𝟙 _

end SmoothProjectiveCurveOverField

/-- A plane cubic over $k$: a nonzero homogeneous polynomial of degree $3$ in three variables. -/
structure PlaneCubic (k : Type*) [Field k] where
  poly : MvPolynomial (Fin 3) k
  isHomogeneous : poly.IsHomogeneous 3
  ne_zero : poly ≠ 0

end
