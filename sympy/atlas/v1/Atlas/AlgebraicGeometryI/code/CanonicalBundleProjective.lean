/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/CanonicalBundleProjective.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalBundleGeneral
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.CanonicalSheafDef
import Lemma.Scheme.Atlas.v1.AlgebraicGeometryI.code.TwistSheaf
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.CanonicalSheafDef
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.TwistSheaf

noncomputable section

open KaehlerDifferential Module CanonicalSheafDef

universe u

section KahlerMvPolynomial

variable (k : Type u) [Field k] (n : ℕ)

/-- Abbreviation for the polynomial ring `k[x₀, …, x_n]` over `k` in `n + 1` variables. -/
abbrev PolyRing := MvPolynomial (Fin (n + 1)) k

/-- Canonical basis of `Ω[k[x₀,…,x_n]⁄k]` given by the `dxᵢ`. -/
def kahlerBasis_mvPolynomial :
    Basis (Fin (n + 1)) (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  mvPolynomialBasis k (Fin (n + 1))

/-- The rank of the Kähler differential module of `k[x₀,…,x_n]` is `n + 1`. -/
theorem kahler_mvPolynomial_finrank :
    Module.finrank (PolyRing k n) (Ω[PolyRing k n⁄k]) = n + 1 := by
  rw [Module.finrank_eq_card_basis (kahlerBasis_mvPolynomial k n), Fintype.card_fin]

/-- The Kähler differential module of `k[x₀,…,x_n]` is finitely generated. -/
instance kahler_mvPolynomial_finite :
    Module.Finite (PolyRing k n) (Ω[PolyRing k n⁄k]) :=
  Module.Finite.of_basis (kahlerBasis_mvPolynomial k n)

/-- Coordinate isomorphism between Kähler differentials of `k[x₀,…,x_n]` and the rank-`(n+1)`
free module. -/
def kahler_mvPolynomial_equivFun :
    Ω[PolyRing k n⁄k] ≃ₗ[PolyRing k n] (Fin (n + 1) → PolyRing k n) :=
  (kahlerBasis_mvPolynomial k n).equivFun

end KahlerMvPolynomial

section MvPolynomialSmooth

variable (k : Type u) [Field k] (n : ℕ)

/-- A polynomial ring `k[x₀, …, x_n]` is smooth of dimension `n + 1` over `k`. -/
instance polyRing_isSmoothOfDimension :
    IsSmoothOfDimension k (PolyRing k n) (n + 1) where
  free := inferInstance
  finite := Module.Finite.of_basis (kahlerBasis_mvPolynomial k n)
  finrank_eq := kahler_mvPolynomial_finrank k n

/-- Type of graded `k`-linear maps in fixed degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinMap (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearMap k k _ _ (RingHom.id k) (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- Type of graded `k`-linear equivalences in degree `d` between two graded modules `M`, `N`. -/
abbrev GrLinEquiv (M N : GradedModuleData.{u, u} k n) (d : ℤ) : Type u :=
  @LinearEquiv k k _ _ (RingHom.id k) (RingHom.id k)
    ⟨RingHom.id_comp _, RingHom.comp_id _⟩ ⟨RingHom.id_comp _, RingHom.comp_id _⟩
    (M.component d) (N.component d)
    (M.instACG d).toAddCommMonoid (N.instACG d).toAddCommMonoid (M.instMod d) (N.instMod d)

/-- A short exact sequence of graded `k`-modules on `P^n`, given by maps in every degree
together with proofs of injectivity, surjectivity and exactness in the middle. -/
structure GradedSES where
  left : GradedModuleData.{u, u} k n
  middle : GradedModuleData.{u, u} k n
  right : GradedModuleData.{u, u} k n
  f : ∀ d : ℤ, GrLinMap k n left middle d
  g : ∀ d : ℤ, GrLinMap k n middle right d
  f_injective : ∀ d : ℤ, Function.Injective (f d)
  g_surjective : ∀ d : ℤ, Function.Surjective (g d)
  exact_middle : ∀ (d : ℤ) (x : middle.component d),
    @Eq (right.component d) (g d x)
      (@Zero.zero (right.component d) (right.instACG d).toAddCommMonoid.toZero) ↔
    ∃ a : left.component d, (f d) a = x

/-- Middle term of the Euler sequence on `P^n`: the direct sum `O(-1)^{n+1}`. -/
def directSumTwist : GradedModuleData.{u, u} k n where
  component d := Fin (n + 1) → (serreTwist k n (-1)).component d
  instACG _d := Pi.addCommGroup
  instMod d := @Pi.module (Fin (n + 1)) (fun _ => (serreTwist k n (-1)).component d) k _
    (fun _ => ((serreTwist k n (-1)).instACG d).toAddCommMonoid)
    (fun _ => (serreTwist k n (-1)).instMod d)
  gsmul i j s v := fun idx =>
    (serreTwist k n (-1)).gsmul i j s (v idx)

/-- The structure sheaf provides a default graded module on `P^n`, giving inhabitedness. -/
instance : Nonempty (GradedModuleData.{u, u} k n) :=
  ⟨structureSheafData k n⟩

/-- The cotangent (Kähler differentials) sheaf on `P^n`, presented as a graded module. -/
opaque cotangentSheafGM : GradedModuleData.{u, u} k n

/-- The canonical bundle of `P^n` (top exterior power of the cotangent sheaf), as a graded
module. By Prop 36 (Lec 20) this equals `O(-(n+1))`. -/
opaque canonicalBundleGM : GradedModuleData.{u, u} k n

/-- Specialisation to `P^1`: `K_{P^1} = O(-2)`. -/
def HasTwistDegree (M : GradedModuleData.{u, u} k n) (d : ℤ) : Prop :=
  ∀ i : ℤ, Nonempty (GrLinEquiv k n M (serreTwist k n d) i)

/-- The canonical bundle of `P^1` has twist degree `-2`, i.e. `K_{P^1} ≅ O(-2)`. -/
end CanonicalBundleProj

end
