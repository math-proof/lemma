import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.Proposition40DegreeMap.Part3
open CategoryTheory Proposition40


namespace Proposition40

/--
[K0Coh.ses_relation](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
lemma K0Coh.ses_relation
  {D : SmoothCompleteCurveCohData.{u,v}}
  {S : ShortComplex D.CohSheaf}
  [Mono S.f]
  [Epi S.g]
-- given
  (hex : S.Exact) :
-- imply
  K0Coh.classOf D S.X₂ = K0Coh.classOf D S.X₁ + K0Coh.classOf D S.X₃ := by
-- proof
  unfold K0Coh.classOf
  rw [← QuotientAddGroup.mk_add]
  apply QuotientAddGroup.eq.mpr
  have hmem : FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ -
    FreeAbelianGroup.of S.X₃ ∈ CohSESRelSubgroup D :=
    AddSubgroup.subset_closure ⟨S, inferInstance, inferInstance, hex, rfl⟩
  have : -FreeAbelianGroup.of S.X₂ + (FreeAbelianGroup.of S.X₁ + FreeAbelianGroup.of S.X₃) =
    -(FreeAbelianGroup.of S.X₂ - FreeAbelianGroup.of S.X₁ - FreeAbelianGroup.of S.X₃) := by
    simp [sub_eq_add_neg]; abel
  rw [this]
  exact (CohSESRelSubgroup D).neg_mem hmem

end Proposition40

namespace Proposition40

/--
[proposition_40_delta_on_class](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
lemma proposition_40_delta_on_class
  {D : SmoothCompleteCurveCohData.{u,v}}
  {ℱ : D.CohSheaf} :
-- imply
  degreeMapK0 D (K0Coh.classOf D ℱ) = D.degree ℱ := by
-- proof
  unfold degreeMapK0 K0Coh.classOf
  simp only [QuotientAddGroup.lift_mk, FreeAbelianGroup.lift_apply_of]

end Proposition40

namespace Proposition40

/--
[proposition_40_delta_well_defined](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
lemma proposition_40_delta_well_defined
  {D : SmoothCompleteCurveCohData.{u,v}} :
-- imply
  ∃ δ : K0Coh D →+ ℤ, ∀ ℱ : D.CohSheaf, δ (K0Coh.classOf D ℱ) = D.degree ℱ :=
-- proof
⟨degreeMapK0 D, proposition_40_delta_on_class D⟩

end Proposition40

namespace Proposition40

/--
[degreeMapK0_ses](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
lemma degreeMapK0_ses
  {D : SmoothCompleteCurveCohData.{u,v}}
  {S : ShortComplex D.CohSheaf}
  [Mono S.f]
  [Epi S.g]
-- given
  (hex : S.Exact) :
-- imply
  degreeMapK0 D (K0Coh.classOf D S.X₂) = degreeMapK0 D (K0Coh.classOf D S.X₁) + degreeMapK0 D (K0Coh.classOf D S.X₃) := by
-- proof
  rw [proposition_40_delta_on_class, proposition_40_delta_on_class,
    proposition_40_delta_on_class]
  exact degree_additive D S hex
end Proposition40


/--
[degree_additive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
private lemma degree_additive_eq
  {D : SmoothCompleteCurveCohData.{u,v}}
  {S : ShortComplex D.CohSheaf}
  [Mono S.f]
  [Epi S.g]
-- given
  (hex : S.Exact) :
-- imply
  D.degree S.X₂ = D.degree S.X₁ + D.degree S.X₃ := by
-- proof
  apply Proposition40.degree_additive D S hex

/--
[degree_lift_ker_contains_relations](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/Proposition40DegreeMap.lean)
-/
@[path]
private lemma degree_lift_ker_contains_relations_eq
  {D : SmoothCompleteCurveCohData.{u,v}} :
-- imply
  CohSESRelSubgroup D ≤ (FreeAbelianGroup.lift D.degree).ker := by
-- proof
  apply Proposition40.degree_lift_ker_contains_relations D


-- created on 2026-10-23
