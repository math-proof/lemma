import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.TangentConeExceptionalLocus
open Polynomial TangentCone


namespace TangentCone

/--
[monomial_mem_reesAlgebra](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean)
-/
@[path]
lemma monomial_mem_reesAlgebra
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
  {a : R}
-- given
  (ha : a ∈ I ^ n) :
-- imply
  Polynomial.monomial n a ∈ reesAlgebra I := by
-- proof
  intro i
  simp only [Polynomial.coeff_monomial]
  split_ifs with h
  · subst h; exact ha
  · exact (I ^ i).zero_mem

end TangentCone

namespace TangentCone

/--
[reesToAssocGraded_surjective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean)
-/
@[path]
lemma reesToAssocGraded_surjective
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {n : ℕ} :
-- imply
  Function.Surjective (reesToAssocGradedComponent R I n) := by
-- proof
  intro x
  obtain ⟨⟨a, ha⟩, hx⟩ := Submodule.Quotient.mk_surjective _ x
  refine ⟨⟨Polynomial.monomial n a, monomial_mem_reesAlgebra R I n a ha⟩, ?_⟩
  simp only [reesToAssocGradedComponent, assocGradedProj, Polynomial.coeff_monomial]
  exact hx

end TangentCone

namespace TangentCone

/--
[reesToAssocGraded_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean)
-/
@[path]
lemma reesToAssocGraded_eq_zero_iff
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {n : ℕ}
  {f : reesAlgebra I} :
-- imply
  reesToAssocGradedComponent R I n f = 0 ↔ (f : Polynomial R).coeff n ∈ (I ^ (n + 1) : Ideal R) := by
-- proof
  unfold reesToAssocGradedComponent assocGradedProj
  constructor
  · intro h
    have hmem : (⟨(↑f : Polynomial R).coeff n, f.2 n⟩ : ↥(I ^ n : Submodule R R)) ∈
      Submodule.comap (I ^ n).subtype (I ^ (n + 1) : Submodule R R) :=
      (Submodule.Quotient.mk_eq_zero _).mp h
    exact hmem
  · exact fun h => (Submodule.Quotient.mk_eq_zero _).mpr h

end TangentCone

namespace TangentCone

/--
[mem_reesAugmentationIdeal_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/TangentConeExceptionalLocus.lean)
-/
@[path]
lemma mem_reesAugmentationIdeal_iff
  {R : Type*}
  [CommRing R]
  {I : Ideal R}
  {f : reesAlgebra I} :
-- imply
  f ∈ reesAugmentationIdeal R I ↔ ∀ n, reesToAssocGradedComponent R I n f = 0 := by
-- proof
  constructor
  · intro hf n; exact (reesToAssocGraded_eq_zero_iff R I n f).mpr (hf n)
  · intro hf n; exact (reesToAssocGraded_eq_zero_iff R I n f).mp (hf n)
/-- The tangent cone `Spec(gr_I(R))` is isomorphic to `Spec` of the quotient of
the Rees algebra by its augmentation ideal, exhibiting the cone over the
exceptional locus of the blowup (Def 38, Lec 19; Prop 38, Lec 20). -/

end TangentCone


-- created on 2026-10-23
