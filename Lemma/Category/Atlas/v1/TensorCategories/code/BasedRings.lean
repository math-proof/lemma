import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.TensorCategories.code.BasedRings
open Finset FusionRing


namespace FusionRing

/--
[duality_trace_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma duality_trace_singleton
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j : ι} :
-- imply
  (∑ k ∈ ({R.unit} : Finset ι), R.N i j k) = if i = R.star j then 1 else 0 := by
-- proof
  simp only [Finset.sum_singleton]
  rw [R.duality]
  congr 1
  exact propext ⟨fun h => by rw [h, R.star_star],
    fun h => by rw [h, R.star_star]⟩

end FusionRing

namespace FusionRing

/--
[star_anti_involution](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma star_anti_involution
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {i j k : ι} :
-- imply
  R.N i j k = R.N (R.star j) (R.star i) (R.star k) := by
-- proof
  have step1 : R.N i j k = R.N j (R.star k) (R.star i) := by
    have assoc_eq := R.assoc i j (R.star k) R.unit
    have lhs_simp : (∑ m : ι, R.N i j m * R.N m (R.star k) R.unit) = R.N i j k := by
      have : ∀ m, R.N m (R.star k) R.unit = if m = k then 1 else 0 := by
        intro m
        rw [R.duality]
        congr 1
        exact propext ⟨fun h => by have := congr_arg R.star h; simp only [R.star_star] at this; exact this.symm,
          fun h => by rw [h]⟩
      simp_rw [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    have rhs_simp : (∑ m : ι, R.N j (R.star k) m * R.N i m R.unit) =
      R.N j (R.star k) (R.star i) := by
      have : ∀ m, R.N i m R.unit = if m = R.star i then 1 else 0 := by
        intro m; exact R.duality i m
      simp_rw [this, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    linarith [assoc_eq]
  have step2 : R.N j (R.star k) (R.star i) = R.N (R.star j) (R.star i) (R.star k) := by
    exact R.N_star_transpose j (R.star k) (R.star i)
  linarith [step1, step2]

end FusionRing

namespace FusionRing

/--
[toMultifusionRingDef_isFusionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma toMultifusionRingDef_isFusionRing
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι} :
-- imply
  R.toMultifusionRingDef.IsFusionRing :=
-- proof
  ⟨R.unit, rfl⟩

end FusionRing

/--
[Proposition_1_42_4_fusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma Proposition_1_42_4_fusion
  [Field κ]
  [CategoryTheory.Category C]
  [CategoryTheory.Preadditive C]
  [CategoryTheory.Linear κ C]
  [CategoryTheory.Abelian C]
  [CategoryTheory.MonoidalCategory C]
  [CategoryTheory.MonoidalPreadditive C]
  [CategoryTheory.MonoidalLinear κ C]
  [CategoryTheory.RigidCategory C]
  [cfd : CategoricalFusionData κ C] :
-- imply
  ∃ (B : MultifusionRingDef cfd.ι), B.N = cfd.N ∧ B.I₀ = {cfd.unitIdx} ∧ B.star = cfd.star ∧ B.IsFusionRing :=
-- proof
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef,
    rfl, rfl, rfl,
    (CategoricalFusionData.toFusionRing).toMultifusionRingDef_isFusionRing⟩

/--
[Proposition_1_42_4_based](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma Proposition_1_42_4_based
  [Field κ]
  [CategoryTheory.Category C]
  [CategoryTheory.Preadditive C]
  [CategoryTheory.Linear κ C]
  [CategoryTheory.Abelian C]
  [CategoryTheory.MonoidalCategory C]
  [CategoryTheory.MonoidalPreadditive C]
  [CategoryTheory.MonoidalLinear κ C]
  [CategoryTheory.RigidCategory C]
  [cfd : CategoricalFusionData κ C] :
-- imply
  ∃ (B : MultifusionRingDef cfd.ι), B.N = cfd.N ∧ B.star = cfd.star :=
-- proof
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef, rfl, rfl⟩

/--
[Proposition_1_42_4_unital](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma Proposition_1_42_4_unital
  [Field κ]
  [CategoryTheory.Category C]
  [CategoryTheory.Preadditive C]
  [CategoryTheory.Linear κ C]
  [CategoryTheory.Abelian C]
  [CategoryTheory.MonoidalCategory C]
  [CategoryTheory.MonoidalPreadditive C]
  [CategoryTheory.MonoidalLinear κ C]
  [CategoryTheory.RigidCategory C]
  [cfd : CategoricalFusionData κ C] :
-- imply
  ∃ (B : MultifusionRingDef cfd.ι), B.N = cfd.N ∧ B.star = cfd.star ∧ ∃ u : cfd.ι, B.I₀ = {u} :=
-- proof
  ⟨(CategoricalFusionData.toFusionRing).toMultifusionRingDef,
    rfl, rfl, (CategoricalFusionData.toFusionRing).toMultifusionRingDef_isFusionRing⟩

namespace FusionRing

/--
[groupRingFusionRing_isFusionRing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma groupRingFusionRing_isFusionRing
  {G : Type*}
  [DecidableEq G]
  [Fintype G]
  [Group G] :
-- imply
  (groupRingFusionRing G).toMultifusionRingDef.IsFusionRing :=
-- proof
  (groupRingFusionRing G).toMultifusionRingDef_isFusionRing

end FusionRing

/--
[Proposition_1_42_9_VecGomega_is_categorification](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
lemma Proposition_1_42_9_VecGomega_is_categorification
  {G : Type*}
  [DecidableEq G]
  [Fintype G]
  [Group G]
  {k : Type*}
  [Field k]
  {ω : NormalizedGroupCocycle3 G kˣ} :
-- imply
  (∀ g h : G, (CG.tensorObj' (⟨g⟩ : CG G kˣ ω) (⟨h⟩ : CG G kˣ ω)).val = g * h) ∧ (CG.unit' : CG G kˣ ω).val = (1 : G) ∧ (∀ g : G, (CG.dualObj (⟨g⟩ : CG G kˣ ω)).val = (FusionRing.groupRingFusionRing G).star g) :=
-- proof
⟨fun g h => rfl, rfl, fun g => rfl⟩

/--
[cocycleCohomologous_refl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
private lemma cocycleCohomologous_refl_eq
  [Group G]
  [CommGroup A]
  {ω : NormalizedGroupCocycle3 G A} :
-- imply
  CocycleCohomologous ω ω := by
-- proof
  apply cocycleCohomologous_refl ω

/--
[cocycleCohomologous_symm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
private lemma cocycleCohomologous_symm_eq
  [Group G]
  [CommGroup A]
  {ω₁ ω₂ : NormalizedGroupCocycle3 G A}
-- given
  (h : CocycleCohomologous ω₁ ω₂) :
-- imply
  CocycleCohomologous ω₂ ω₁ := by
-- proof
  apply cocycleCohomologous_symm h

/--
[cocycleCohomologous_trans](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRings.lean)
-/
@[path]
private lemma cocycleCohomologous_trans_eq
  [Group G]
  [CommGroup A]
  {ω₁ ω₂ ω₃ : NormalizedGroupCocycle3 G A}
-- given
  (h₁₂ : CocycleCohomologous ω₁ ω₂)
  (h₂₃ : CocycleCohomologous ω₂ ω₃) :
-- imply
  CocycleCohomologous ω₁ ω₃ := by
-- proof
  apply cocycleCohomologous_trans h₁₂ h₂₃


-- created on 2026-10-23
