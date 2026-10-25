/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/LindemannWeierstrass.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado
-/

import Mathlib.Analysis.Complex.Exponential
import Mathlib.RingTheory.Algebraic.Defs
import Mathlib.Algebra.Group.UniqueProds.VectorSpace
import Mathlib.Algebra.MonoidAlgebra.NoZeroDivisors
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Nat.Prime.Int
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.FieldTheory.Normal.Basic
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.NumberTheory.Transcendental.Lindemann.AnalyticalPart
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.IsGaloisGroup.Defs
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Topology.Algebra.Order.Floor


section

namespace MathlibExt.NumberTheory.LindemannWeierstrassWanted

/-- The exponential character `K → ℂ`. -/
noncomputable def lw_expHom {K : IntermediateField ℚ ℂ} : Multiplicative K →* ℂ :=
  Complex.expMonoidHom.comp (AddMonoidHom.toMultiplicative K.val.toAddMonoidHom)

/-- Evaluation of `K`-coefficient exponential polynomials. -/
noncomputable def lw_evK {K : IntermediateField ℚ ℂ} :
    AddMonoidAlgebra K K →ₐ[K] ℂ :=
  AddMonoidAlgebra.lift K ℂ K lw_expHom

/-- Evaluation of `ℚ`-coefficient exponential polynomials. -/
noncomputable def lw_evQ {K : IntermediateField ℚ ℂ} :
    AddMonoidAlgebra ℚ K →ₐ[ℚ] ℂ :=
  AddMonoidAlgebra.lift ℚ ℂ K lw_expHom

open Classical in
/-- Coefficient norm over the Galois group. -/
noncomputable def lw_coeffNorm {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (E : AddMonoidAlgebra K K) :
    AddMonoidAlgebra K K :=
  ∏ σ : (K ≃ₐ[ℚ] K), AddMonoidAlgebra.mapRingHom K (σ : K →+* K) E

open Classical in
/-- Exponent norm over the Galois group. -/
noncomputable def lw_expNorm {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] (E₂ : AddMonoidAlgebra ℚ K) :
    AddMonoidAlgebra ℚ K :=
  ∏ σ : (K ≃ₐ[ℚ] K),
    AddMonoidAlgebra.mapDomainRingHom ℚ (σ : K →+ K) E₂

open Classical in
/-- Reflection as a ring hom on the group ring. -/
noncomputable def lw_refl {K : IntermediateField ℚ ℂ}
    [FiniteDimensional ℚ K] [IsGalois ℚ K] :
    AddMonoidAlgebra ℚ K →+* AddMonoidAlgebra ℚ K :=
  AddMonoidAlgebra.mapDomainRingHom ℚ (negAddMonoidHom : K →+ K)

end MathlibExt.NumberTheory.LindemannWeierstrassWanted
end
