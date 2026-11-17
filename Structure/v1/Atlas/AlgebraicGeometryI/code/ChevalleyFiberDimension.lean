/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ChevalleyFiberDimension.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Theorem.v1.Atlas.AlgebraicGeometryI.code.ChevalleyImage
public import Theorem.Scheme.Atlas.v1.AlgebraicGeometryI.code.ChevalleyImage
public import Mathlib.RingTheory.Spectrum.Prime.Noetherian
public import Def.v1.Atlas.AlgebraicGeometryI.code.ChevalleyFiberDimension


public noncomputable section

open PrimeSpectrum Topology

namespace ChevalleyFiberDim

/-- The bundled data of a dominant morphism of integral schemes of finite type:
the algebra map is injective, the algebra is finite type, and we record the transcendence degree
of the function field extension. -/
structure DominantFiniteTypeMorphism (B A : Type*) [CommRing B] [CommRing A]
    [IsDomain B] [IsDomain A] [IsNoetherianRing B] [Algebra B A] where
  injective : Function.Injective (algebraMap B A)
  finiteType : Algebra.FiniteType B A
  transDeg : ℕ

/-- Noether normalization descent: for a dominant finite-type morphism between integral domains,
after inverting some nonzero `b ∈ B`, the localized algebra `A[b⁻¹]` is finite over a polynomial
ring `B[b⁻¹][x₁,…,xₙ]`, and the basic open `D(b)` lies in the image. -/
structure Lemma33Data (B A : Type*) [CommRing B] [CommRing A] [Algebra B A] where
  b : B
  hb : b ≠ 0
  n : ℕ
  φ : MvPolynomial (Fin n) (Localization.Away b) →+*
      Localization.Away ((algebraMap B A) b)
  φ_finite : φ.Finite
  φ_injective : Function.Injective φ
  φ_compat : φ.comp MvPolynomial.C = Localization.awayMap (algebraMap B A) b
  basicOpen_sub_image :
    (↑(basicOpen b) : Set (PrimeSpectrum B)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap B A))

end ChevalleyFiberDim
end
