/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CohomologyAxiomsElimination.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ZariskiSheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.ZariskiSheafCohomology
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.H0GlobalSections
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.H0GlobalSections

open AlgebraicGeometry CategoryTheory CategoryTheory.Abelian TopologicalSpace
open ZariskiSheafCohomology

noncomputable section


namespace CohomologyAxiomsElimination

/-- Concrete definition of `h^1(O)` for an affine curve `Spec A` over `k`: the `k`-dimension of
the Kähler differentials `Ω_{A/k}`. -/
def h1_O_defined (k : Type*) [Field k] (A : Type*) [CommRing A]
    [Algebra k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- Concrete definition of `h^1(skyscraper)`: zero, since the cohomology of a skyscraper sheaf
vanishes in positive degree. -/
def h1_sky_defined (_k : Type*) [Field _k] (_A : Type*) : ℕ := 0


/-- The `h^1(O)` of the affine spectrum `Spec R`, computed from the abstract sheaf cohomology. -/
def h1_O_sheafH (k : Type*) [Field k] (R : CommRingCat)
    [Module k (sheafCohomology (Scheme.Spec.obj (Opposite.op R)) 1)] : ℕ :=
  specH k (Scheme.Spec.obj (Opposite.op R)) 1

/-- The `h^0(O)` of the affine spectrum `Spec R`, computed from the abstract sheaf cohomology. -/
def h0_O_sheafH (k : Type*) [Field k] (R : CommRingCat)
    [Module k (sheafCohomology (Scheme.Spec.obj (Opposite.op R)) 0)] : ℕ :=
  specH k (Scheme.Spec.obj (Opposite.op R)) 0


/-- The "grounded" Euler characteristic homomorphism `ℤ × ℤ → ℤ` for a Dedekind curve, built
from the concrete `h1_O_defined` and `h1_sky_defined` values. -/
def groundedCohChi {k : Type*} [Field k] (C : DedekindCurve k) : ℤ × ℤ →+ ℤ where
  toFun p := p.1 * (1 - (h1_O_defined k C.A : ℤ)) + p.2 * (1 - (h1_sky_defined k C.A : ℤ))
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring


/-- `H^0` agrees with global sections (alias). -/
def h0_equiv_sections (X : Scheme) :=
  h0EquivGlobalSections X

/-- Global sections of `O_{Spec R}` are `R` (alias). -/
def specGlobalSections (R : CommRingCat) :=
  globalSections_Spec_iso R


end CohomologyAxiomsElimination

end
