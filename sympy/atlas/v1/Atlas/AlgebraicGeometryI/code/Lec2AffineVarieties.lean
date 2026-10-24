/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Lec2AffineVarieties.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.AlgebraicGeometry.Properties
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Affine
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Scheme
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.FiniteType
import Mathlib.Topology.NoetherianSpace
import Mathlib.Topology.Sheaves.Sheaf

open AlgebraicGeometry CategoryTheory TopologicalSpace

noncomputable section

universe u

/-- Definition 3: An algebraic variety over `k` is a scheme `X` with a morphism `f : X → Spec k`
that is locally of finite type, quasicompact, and whose total space is reduced. -/
class Definition3_AlgebraicVariety (k : Type u) [Field k]
    (X : Scheme.{u}) (f : X ⟶ Spec (CommRingCat.of k)) : Prop where
  locallyOfFiniteType : LocallyOfFiniteType f
  quasiCompact : QuasiCompact f
  reduced : AlgebraicGeometry.IsReduced X

/-- The natural ℕ-grading of `k[x₀, …, xₙ]` by total degree, used to define `ℙⁿ_k = Proj`. -/
def polynomialGrading (k : Type u) [Field k] (n : ℕ) :=
  MvPolynomial.homogeneousSubmodule (Fin (n + 1)) k

/-- The degree-grading of `k[x₀, …, xₙ]` gives it the structure of a graded ring. -/
instance polynomialGradedRing (k : Type u) [Field k] (n : ℕ) :
    GradedRing (polynomialGrading k n) :=
  MvPolynomial.gradedAlgebra

/-- Definition 4: The projective `n`-space `ℙⁿ_k`, realised as `Proj k[x₀, …, xₙ]`. -/
def Definition4_ProjectiveSpace (k : Type u) [Field k] (n : ℕ) : Scheme :=
  AlgebraicGeometry.Proj (polynomialGrading k n)

/-- The underlying topological space of `ℙⁿ_k`. -/
instance Definition4_ProjectiveSpace_topologicalSpace (k : Type u) [Field k] (n : ℕ) :
    TopologicalSpace (Definition4_ProjectiveSpace k n) :=
  inferInstance

/-- The structure sheaf `O_{ℙⁿ_k}` of projective space. -/
def Definition4_structureSheaf (k : Type u) [Field k] (n : ℕ) :
    TopCat.Presheaf CommRingCat (Definition4_ProjectiveSpace k n).carrier :=
  (Definition4_ProjectiveSpace k n).presheaf
