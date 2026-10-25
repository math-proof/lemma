import Mathlib
import sympy.Basic
import Lemma.UpperHalfPlane.FormalUpperHalfPlaneFrame
open CerednikDrinfeld.Omega CerednikDrinfeld.FormalOmega


/--
In an adic frame, valuation of the uniformizer image is strictly less than one.
-/
@[path]
private lemma main
  {𝒪 : Type} [CommRing 𝒪]
  {K : Type} [Field K] [Algebra 𝒪 K]
  {C : Type} [Field C] [Algebra K C] [Algebra 𝒪 C] [IsScalarTower 𝒪 K C]
  {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued C Γ₀]
  {R : Type} [CommRing R] [Algebra 𝒪 R] [Algebra R C] [IsScalarTower 𝒪 R C]
  {π : 𝒪}
  {ϖ : PseudoUniformizer K C}
-- given
  (h : IsAdicFrame π ϖ R) :
-- imply
  Valued.v (algebraMap 𝒪 C π) < 1 := by
-- proof
  simpa [h.unif] using ϖ.lt_one


-- created on 2026-10-24
