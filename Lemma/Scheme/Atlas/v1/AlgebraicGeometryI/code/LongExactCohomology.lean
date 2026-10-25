import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LongExactCohomology
open CategoryTheory CategoryTheory.Limits HomologicalComplex LongExactCohomology


namespace LongExactCohomology

/--
[long_exact_seq_exact_at_H_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean)
-/
@[path]
lemma long_exact_seq_exact_at_H_A
  {𝒜 : Type u}
  [Category.{v} 𝒜]
  [Abelian 𝒜]
  {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
  {n : ℤ}
-- given
  (hS : S.ShortExact) :
-- imply
  (CategoryTheory.ShortComplex.mk (connectingHomomorphism hS n) (HomologicalComplex.homologyMap S.f (n + 1)) (hS.δ_comp n (n + 1) (up_rel n))).Exact :=
-- proof
  hS.homology_exact₁ n (n + 1) (up_rel n)

end LongExactCohomology

namespace LongExactCohomology

/--
[long_exact_seq_exact_at_H_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean)
-/
@[path]
lemma long_exact_seq_exact_at_H_B
  {𝒜 : Type u}
  [Category.{v} 𝒜]
  [Abelian 𝒜]
  {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
  {n : ℤ}
-- given
  (hS : S.ShortExact) :
-- imply
  (CategoryTheory.ShortComplex.mk (HomologicalComplex.homologyMap S.f n) (HomologicalComplex.homologyMap S.g n) (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])).Exact :=
-- proof
  CategoryTheory.ShortComplex.ShortExact.homology_exact₂ hS n

end LongExactCohomology

namespace LongExactCohomology

/--
[long_exact_seq_exact_at_H_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean)
-/
@[path]
lemma long_exact_seq_exact_at_H_C
  {𝒜 : Type u}
  [Category.{v} 𝒜]
  [Abelian 𝒜]
  {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
  {n : ℤ}
-- given
  (hS : S.ShortExact) :
-- imply
  (CategoryTheory.ShortComplex.mk (HomologicalComplex.homologyMap S.g n) (connectingHomomorphism hS n) (hS.comp_δ n (n + 1) (up_rel n))).Exact :=
-- proof
  hS.homology_exact₃ n (n + 1) (up_rel n)

end LongExactCohomology

namespace LongExactCohomology

/--
[long_exact_cohomology_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean)
-/
@[path]
lemma long_exact_cohomology_sequence
  {𝒜 : Type u}
  [Category.{v} 𝒜]
  [Abelian 𝒜]
  {S : CategoryTheory.ShortComplex (CochainComplex 𝒜 ℤ)}
  {n : ℤ}
-- given
  (hS : S.ShortExact) :
-- imply
  (CategoryTheory.ShortComplex.mk (HomologicalComplex.homologyMap S.f n) (HomologicalComplex.homologyMap S.g n) (by rw [← HomologicalComplex.homologyMap_comp, S.zero, HomologicalComplex.homologyMap_zero])).Exact ∧ (CategoryTheory.ShortComplex.mk (HomologicalComplex.homologyMap S.g n) (connectingHomomorphism hS n) (hS.comp_δ n (n + 1) (up_rel n))).Exact ∧ (CategoryTheory.ShortComplex.mk (connectingHomomorphism hS n) (HomologicalComplex.homologyMap S.f (n + 1)) (hS.δ_comp n (n + 1) (up_rel n))).Exact :=
-- proof
  ⟨long_exact_seq_exact_at_H_B hS n,
    long_exact_seq_exact_at_H_C hS n,
    long_exact_seq_exact_at_H_A hS n⟩

end LongExactCohomology

/--
[up_rel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactCohomology.lean)
-/
@[path]
private lemma up_rel_eq
  {𝒜 : Type u}
  [Category.{v} 𝒜]
  [Abelian 𝒜]
  {n : ℤ} :
-- imply
  (ComplexShape.up ℤ).Rel n (n + 1) := by
-- proof
  apply LongExactCohomology.up_rel n


-- created on 2026-10-23
