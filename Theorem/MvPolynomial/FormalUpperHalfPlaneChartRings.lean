module

public import Mathlib
public import Def.CerednikDrinfeld_FormalUpperHalfPlaneCharts
public import Instance.CerednikDrinfeld_FormalUpperHalfPlaneChartRings
public import Abbrev.CerednikDrinfeld_FormalUpperHalfPlaneChartRings

public noncomputable section

set_option autoImplicit false

noncomputable section

open Polynomial

namespace CerednikDrinfeld
namespace FormalOmega

section ChartRings

variable (R : Type) [CommRing R]

namespace chartVRing

variable (q : ℕ)


public theorem algebraMap_vertexDiscr : algebraMap R[X] (chartVRing R q) (vertexDiscr R q) = ζ R q ^ q - ζ R q := by
  show algebraMap R[X] (chartVRing R q) (X ^ q - X) = _
  rw [map_sub, map_pow]; rfl


public theorem isUnit_ζ_pow_sub : IsUnit (ζ R q ^ q - ζ R q) := by
  rw [← algebraMap_vertexDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (vertexDiscr R q)


public theorem isUnit_aeval_of_mem_powers {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B)
    (y : Submonoid.powers (vertexDiscr R q)) : IsUnit (Polynomial.aeval (R := R) x.1 (y : R[X])) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  have : Polynomial.aeval (R := R) x.1 (vertexDiscr R q) = x.1 ^ q - x.1 := by
    show Polynomial.aeval (R := R) x.1 (X ^ q - X) = _
    rw [map_sub (Polynomial.aeval (R := R) x.1), map_pow (Polynomial.aeval (R := R) x.1), Polynomial.aeval_X]
  rw [this]; exact x.2


@[simp] public theorem lift_ζ {B : Type} [CommRing B] [Algebra R B] (x : (chartV R q).obj B) : lift x (ζ R q) = x.1 := by
  rw [lift, IsLocalization.liftAlgHom_apply, ζ, IsLocalization.lift_eq]
  exact Polynomial.aeval_X x.1

variable (R q) in


@[simp] public theorem corepEquiv_apply_val (B : Type) [CommRing B] [Algebra R B] (φ : chartVRing R q →ₐ[R] B) :
    (corepEquiv R q B φ).1 = φ (ζ R q) := rfl


public theorem corepEquiv_natural {B : Type} [CommRing B] [Algebra R B] {B' : Type} [CommRing B'] [Algebra R B']
    (f : B →ₐ[R] B') (φ : chartVRing R q →ₐ[R] B) :
    corepEquiv R q B' ((AlgFunctor.corep (𝒪 := R) (chartVRing R q)).map f φ) = (chartV R q).map f (corepEquiv R q B φ) :=
  Subtype.ext rfl

variable (R q) in


public theorem edgeQuot.mk_edgeRel (π : R) : edgeQuot.mk R π (edgeRel R π) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))


public theorem ofPoly_edgeRel : ofPoly R π q (edgeRel R π) = 0 := by
  rw [ofPoly, AlgHom.comp_apply, edgeQuot.mk_edgeRel, map_zero]


public theorem ξ_mul_η : ξ R π q * η R π q = algebraMap R (chartERing R π q) π := by
  have hC : ofPoly R π q (MvPolynomial.C π) = algebraMap R (chartERing R π q) π := (ofPoly R π q).commutes π
  have h2 : ofPoly R π q (edgeRel R π) = ξ R π q * η R π q - algebraMap R (chartERing R π q) π := by
    show ofPoly R π q (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = _
    rw [map_sub (ofPoly R π q), map_mul (ofPoly R π q), hC]; rfl
  rw [← sub_eq_zero, ← h2, ofPoly_edgeRel]


public theorem ofPoly_edgeDiscr :
    ofPoly R π q (edgeDiscr R q) = (ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1) := by
  show ofPoly R π q ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)) = _
  rw [map_mul (ofPoly R π q), map_sub (ofPoly R π q), map_sub (ofPoly R π q), map_pow (ofPoly R π q),
    map_pow (ofPoly R π q), map_one]; rfl


public theorem isUnit_discr : IsUnit ((ξ R π q ^ (q - 1) - 1) * (η R π q ^ (q - 1) - 1)) := by
  rw [← ofPoly_edgeDiscr]
  exact IsLocalization.Away.algebraMap_isUnit (edgeQuot.discr R π q)


@[simp] public theorem evalPoly_X_zero {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 0) = x.1.1 := by simp [evalPoly, MvPolynomial.aeval_X]


@[simp] public theorem evalPoly_X_one {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (MvPolynomial.X 1) = x.1.2 := by simp [evalPoly, MvPolynomial.aeval_X]


public theorem evalPoly_edgeRel {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) :
    evalPoly x (edgeRel R π) = 0 := by
  have hC : evalPoly x (MvPolynomial.C π) = algebraMap R B π := (evalPoly x).commutes π
  show evalPoly x (MvPolynomial.X 0 * MvPolynomial.X 1 - MvPolynomial.C π) = 0
  rw [map_sub (evalPoly x), map_mul (evalPoly x), evalPoly_X_zero, evalPoly_X_one, hC, x.2.1, sub_self]


public theorem evalQuot_mk {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) (p : MvPolynomial (Fin 2) R) :
    evalQuot x (edgeQuot.mk R π p) = evalPoly x p := rfl


public theorem isUnit_evalQuot_of_mem_powers {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B)
    (y : Submonoid.powers (edgeQuot.discr R π q)) :
    IsUnit (evalQuot x (y : edgeQuot R π)) := by
  obtain ⟨_, n, rfl⟩ := y
  rw [map_pow]
  refine IsUnit.pow n ?_
  rw [edgeQuot.discr, evalQuot_mk]
  show IsUnit (evalPoly x ((MvPolynomial.X 0 ^ (q - 1) - 1) * (MvPolynomial.X 1 ^ (q - 1) - 1)))
  rw [map_mul (evalPoly x), map_sub (evalPoly x), map_sub (evalPoly x), map_pow (evalPoly x), map_pow (evalPoly x),
    map_one, evalPoly_X_zero, evalPoly_X_one]
  exact x.2.2.1.mul x.2.2.2


public theorem lift_ofPoly {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) (p : MvPolynomial (Fin 2) R) :
    lift x (ofPoly R π q p) = evalPoly x p := by
  rw [lift, IsLocalization.liftAlgHom_apply, ofPoly, AlgHom.comp_apply]
  exact (IsLocalization.lift_eq _ _).trans (evalQuot_mk x p)


@[simp] public theorem lift_ξ {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : lift x (ξ R π q) = x.1.1 := by
  rw [ξ, lift_ofPoly, evalPoly_X_zero]


@[simp] public theorem lift_η {B : Type} [CommRing B] [Algebra R B] (x : (chartE R π q).obj B) : lift x (η R π q) = x.1.2 := by
  rw [η, lift_ofPoly, evalPoly_X_one]

variable (R π q) in


@[simp] public theorem corepEquiv_apply_val (B : Type) [CommRing B] [Algebra R B] (φ : chartERing R π q →ₐ[R] B) :
    (corepEquiv R π q B φ).1 = (φ (ξ R π q), φ (η R π q)) := rfl


public theorem corepEquiv_natural {B : Type} [CommRing B] [Algebra R B] {B' : Type} [CommRing B'] [Algebra R B']
    (f : B →ₐ[R] B') (φ : chartERing R π q →ₐ[R] B) :
    corepEquiv R π q B' ((AlgFunctor.corep (𝒪 := R) (chartERing R π q)).map f φ) = (chartE R π q).map f (corepEquiv R π q B φ) :=
  Subtype.ext rfl

variable (R π q) in


public theorem isNilpotent_algebraMap_of_isScalarTower (B : Type) [CommRing B] [Algebra 𝒪 B]
    [Algebra (truncRing 𝒪 π n) B] [IsScalarTower 𝒪 (truncRing 𝒪 π n) B] : IsNilpotent (algebraMap 𝒪 B π) := by
  refine ⟨n + 1, ?_⟩
  rw [← map_pow, IsScalarTower.algebraMap_apply 𝒪 (truncRing 𝒪 π n) B,
    Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _)),
    map_zero]

end Level

end ChartRings

end FormalOmega
end CerednikDrinfeld

end
