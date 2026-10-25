/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/DedekindCurve.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.RiemannRochCurves
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafCurves
import Def.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafCurves.Part2
import Structure.v1.Atlas.AlgebraicGeometryI.code.DedekindCurve
set_option maxHeartbeats 1600000

open scoped TensorProduct
open nonZeroDivisors
open RiemannRochCurves CanonicalSheafCurves


noncomputable section

attribute [instance] DedekindCurve.instCR DedekindCurve.instID DedekindCurve.instDD
  DedekindCurve.instAlg DedekindCurve.instFin

namespace DedekindCurve

variable {k : Type*} [Field k]


/-- The genus of a Dedekind curve, defined as the `k`-dimension of its global Kähler
differentials `Ω[A⁄k]`. -/
def ddGenus (C : DedekindCurve k) : ℕ :=
  Module.finrank k (Ω[C.A⁄k])

/-- Degree of an ideal `I` on a Dedekind curve `C`, measured as `dim_k (A/I)`. -/
def curveIdealDeg (C : DedekindCurve k) (I : Ideal C.A) : ℕ :=
  Module.finrank k (C.A ⧸ I)

/-- The generic rank of an `A`-module `M` on the curve `C`, defined as the dimension of
its localization at the generic point. -/
def curveModuleRk (C : DedekindCurve k) (M : Type*) [AddCommGroup M] [Module C.A M] : ℕ :=
  Module.finrank (FractionRing C.A) (FractionRing C.A ⊗[C.A] M)


/-- The Euler characteristic of the structure sheaf of a Dedekind curve: `χ(O_X) = 1 - g`. -/
def eulerCharO (C : DedekindCurve k) : ℤ :=
  1 - (C.ddGenus : ℤ)

/-- The degree of the canonical divisor on a Dedekind curve: `deg K = 2g - 2`. -/
def degK (C : DedekindCurve k) : ℤ :=
  2 * (C.ddGenus : ℤ) - 2


end DedekindCurve

/-- `h¹(O_X)` for a Dedekind curve, defined via `dim_k Ω[A⁄k]` using Serre duality. -/
noncomputable def DedekindCurve.h1_O (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- `H¹` of a skyscraper sheaf on a Dedekind curve vanishes (by dimension); modeled as `0`. -/
def DedekindCurve.h1_sky (_k : Type*) [Field _k] (_A : Type*) [CommRing _A] [IsDomain _A]
    [IsDedekindDomain _A] [Algebra _k _A] [Module.Finite _k _A] : ℕ :=
  0

/-- The additive Euler-characteristic homomorphism on the K-theory generators
`(rank, degree)`, sending `(r, d)` to `r·χ(O_X) + d·χ(sky)`. -/
def cohChi (C : DedekindCurve k) : ℤ × ℤ →+ ℤ where
  toFun p := p.1 * (1 - (h1_O k C.A : ℤ)) + p.2 * (1 - (h1_sky k C.A : ℤ))
  map_zero' := by simp
  map_add' := by intro ⟨r₁, d₁⟩ ⟨r₂, d₂⟩; simp; ring

/-- Repackage a Dedekind curve as an abstract `SmoothCompleteCurve` carrying genus,
Euler characteristic, and canonical degree. -/
def toSmoothCompleteCurve (C : DedekindCurve k) : SmoothCompleteCurve where
  g := C.ddGenus
  χ := C.cohChi
  degK := C.degK
  hg_nonneg := Int.natCast_nonneg C.ddGenus
  hχ_struct := C.cohChi_struct_eq
  hχ_sky := C.cohChi_sky_eq
  hwf := CanonicalSheafCurves.curveWitness_of_nat C.ddGenus


/-- Sheaf-level `h¹(O_X)` for a Dedekind curve, again defined via `dim_k Ω[A⁄k]`. -/
def h1_O_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℕ :=
  Module.finrank k (Ω[A⁄k])

/-- Sheaf-level Euler characteristic of `O_X` for a Dedekind curve: `1 - g`. -/
def eulerCharO_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℤ :=
  1 - (Module.finrank k (Ω[A⁄k]) : ℤ)

/-- Sheaf-level degree of the canonical divisor of a Dedekind curve: `2g - 2`. -/
def degK_sheaf (k : Type*) [Field k] (A : Type*) [CommRing A] [IsDomain A]
    [IsDedekindDomain A] [Algebra k A] [Module.Finite k A] : ℤ :=
  2 * (Module.finrank k (Ω[A⁄k]) : ℤ) - 2

end
