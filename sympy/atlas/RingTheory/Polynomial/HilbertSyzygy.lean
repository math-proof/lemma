/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/RingTheory/Polynomial/HilbertSyzygy.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.RingTheory.Finiteness.Basic
import Mathlib.Algebra.Category.ModuleCat.ProjectiveDimension
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.Algebra.Polynomial.Module.TensorProduct
import Mathlib.Algebra.MvPolynomial.Equiv
import Mathlib.RingTheory.MvPolynomial.Basic
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Finsupp.Pi
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.Algebra.Exact.Basic
import Mathlib.Logic.Small.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Basic

open CategoryTheory Polynomial TensorProduct

noncomputable section

universe u v

namespace MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted

/-- `hs_AllLE R d`: every object of `ModuleCat.{v} R` has projective dimension `≤ d`. -/
private def hs_AllLE (R : Type u) [Ring R] (d : ℕ) : Prop :=
  ∀ (N : ModuleCat.{v} R), CategoryTheory.HasProjectiveDimensionLE N d

/-- `hs_mapX f`: the `R[X]`-linear extension of `PolynomialModule.map R f`. -/
private def hs_mapX {R : Type u} [CommRing R] {L L' : Type v}
    [AddCommGroup L] [Module R L] [AddCommGroup L'] [Module R L']
    (f : L →ₗ[R] L') : PolynomialModule R L →ₗ[R[X]] PolynomialModule R L' where
  toFun := PolynomialModule.map R f
  map_add' := map_add _
  map_smul' := fun p q => by
    change PolynomialModule.map R f (p • q) = p • PolynomialModule.map R f q
    rw [PolynomialModule.map_smul, Algebra.algebraMap_self, Polynomial.map_id]

section hs_char
/-- Multiply by `X` as an `R`-linear endomorphism. -/
private def hs_xAct : N →ₗ[R] N :=
  ((Polynomial.X : R[X]) • (LinearMap.id : N →ₗ[R[X]] N)).restrictScalars R

/-- Evaluation of coefficients: `Σ single i mᵢ ↦ Σ Xⁱ • mᵢ`. -/
private def hs_phi : PolynomialModule R N →ₗ[R[X]] N :=
  (LinearMap.liftBaseChange R[X] (LinearMap.id : N →ₗ[R] N)).comp
    (PolynomialModule.polynomialTensorProductLEquivPolynomialModule R N).symm.toLinearMap

/-- `p ↦ X • p − (X acting on each coefficient)`. -/
private def hs_psi : PolynomialModule R N →ₗ[R[X]] PolynomialModule R N :=
  (Polynomial.X : R[X]) • (LinearMap.id : PolynomialModule R N →ₗ[R[X]] _) -
    hs_mapX hs_xAct
end hs_char
end MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted
namespace MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted
end MathlibExt.RingTheory.Polynomial.HilbertSyzygyWanted
