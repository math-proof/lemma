import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part8
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory SingularCohomology
open scoped TensorProduct
open SingularCohomology
open scoped Simplicial
open Opposite SimplexCategory


namespace SingularCohomology

/--
[face₁_oneSimplexOfPath](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
the starting point `x`. -/
lemma face₁_oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) :
  sing0EquivX X (face₁ X (oneSimplexOfPath X γ)) = x := by
  simp only [face₁, oneSimplexOfPath]
  rw [sing0EquivX_face_eq]
  simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk, Function.comp]
  rwa [stdSimplex_map_δ1_default, stdSimplexHomeomorphUnitInterval_zero]

end SingularCohomology

namespace SingularCohomology

/--
[face₀_oneSimplexOfPath](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
the endpoint `y`. -/
lemma face₀_oneSimplexOfPath (X : TopCat.{0}) {x y : X} (γ : Path x y) :
  sing0EquivX X (face₀ X (oneSimplexOfPath X γ)) = y := by
  simp only [face₀, oneSimplexOfPath]
  rw [sing0EquivX_face_eq]
  simp only [Equiv.apply_symm_apply, ContinuousMap.coe_mk, Function.comp]
  rwa [stdSimplex_map_δ0_default, stdSimplexHomeomorphUnitInterval_one]

end SingularCohomology

/--
[ofHom_add_hom_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma ofHom_add_hom_eq_eq
  {R : Type}
  [CommRing R]
  {f g : R →ₗ[R] R} :
-- imply
  (ModuleCat.ofHom f + ModuleCat.ofHom g).hom = f + g := by
-- proof
  apply SingularCohomology.ofHom_add_hom_eq R f g

/--
[sing0EquivX_face_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma sing0EquivX_face_eq_eq
  {X : TopCat.{0}}
  {i : Fin 2}
  {σ : Sing 1 X} :
-- imply
  sing0EquivX X ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ) = (TopCat.toSSetObjEquiv X (op ⦋1⦌) σ).1 (_root_.stdSimplex.map (SimplexCategory.δ i).toOrderHom default) := by
-- proof
  apply SingularCohomology.sing0EquivX_face_eq X i σ

/--
[stdSimplex_map_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma stdSimplex_map__eq :
-- imply
  (_root_.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)).toOrderHom (default : stdSimplex ℝ (Fin 1))) = ⟨Pi.single 0 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
-- proof
  apply SingularCohomology.stdSimplex_map_

/--
[stdSimplex_map_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma stdSimplex_map__eq_2 :
-- imply
  (_root_.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)).toOrderHom (default : stdSimplex ℝ (Fin 1))) = ⟨Pi.single 1 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
-- proof
  apply SingularCohomology.stdSimplex_map_

/--
[face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma face_eq
  {X : TopCat.{0}}
  {x y : X}
  {γ : Path x y} :
-- imply
  sing0EquivX X (face₁ X (oneSimplexOfPath X γ)) = x := by
-- proof
  apply SingularCohomology.face X γ

/--
[face](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma face_eq_2
  {X : TopCat.{0}}
  {x y : X}
  {γ : Path x y} :
-- imply
  sing0EquivX X (face₀ X (oneSimplexOfPath X γ)) = y := by
-- proof
  apply SingularCohomology.face X γ

/--
[joined_of_one_simplex](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma joined_of_one_simplex_eq
  {X : TopCat.{0}}
  {σ : Sing 1 X} :
-- imply
  Joined (sing0EquivX X (face₁ X σ)) (sing0EquivX X (face₀ X σ)) := by
-- proof
  apply SingularCohomology.joined_of_one_simplex X σ

/--
[singularChainZ_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma singularChainZ__eq
  {X : TopCat.{0}}
  {σ : Sing 1 X} :
-- imply
  Sigma.ι (fun (_ : Sing 1 X) => ModuleCat.of ℤ ℤ) σ ≫ (singularChainZ X).d 1 0 = Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₀ X σ) - Sigma.ι (fun (_ : Sing 0 X) => ModuleCat.of ℤ ℤ) (face₁ X σ) := by
-- proof
  apply SingularCohomology.singularChainZ_ X σ

/--
[coboundary_zero_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma coboundary_zero_eval_eq
  {X : TopCat.{0}}
  {N : ModuleCat.{0} ℤ}
  {f : (singularCochainComplex ℤ X N).X 0}
  {σ : Sing 1 X} :
-- imply
  cochainEvalN X N 1 ((singularCochainComplex ℤ X N).d 0 1 f) σ = cochainEvalN X N 0 f (face₀ X σ) - cochainEvalN X N 0 f (face₁ X σ) := by
-- proof
  apply SingularCohomology.coboundary_zero_eval X N f σ

/--
[cochainOfFunc_eval](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma cochainOfFunc_eval_eq
  {X : TopCat.{0}}
  {N : ModuleCat.{0} ℤ}
  {g : X → N}
  {σ₀ : Sing 0 X} :
-- imply
  cochainEvalN X N 0 (cochainOfFunc X N g) σ₀ = g (sing0EquivX X σ₀) := by
-- proof
  apply SingularCohomology.cochainOfFunc_eval X N g σ₀

/--
[moduleCat_int_hom_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma moduleCat_int_hom_ext_eq
  {N : ModuleCat.{0} ℤ}
  {φ ψ : ModuleCat.of ℤ ℤ ⟶ N}
-- given
  (h : φ.hom (1 : ℤ) = ψ.hom (1 : ℤ)) :
-- imply
  φ = ψ := by
-- proof
  apply SingularCohomology.moduleCat_int_hom_ext φ ψ h

/--
[cochain_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma cochain_ext_eq
  {X : TopCat.{0}}
  {N : ModuleCat.{0} ℤ}
  {f₁ f₂ : (singularCochainComplex ℤ X N).X 0}
-- given
  (h : ∀ σ₀ : Sing 0 X, cochainEvalN X N 0 f₁ σ₀ = cochainEvalN X N 0 f₂ σ₀) :
-- imply
  f₁ = f₂ := by
-- proof
  apply SingularCohomology.cochain_ext X N f₁ f₂ h

/--
[cochain1_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean)
-/
@[path]
private lemma cochain1_eq_zero_iff_eq
  {X : TopCat.{0}}
  {N : ModuleCat.{0} ℤ}
  {f : (singularCochainComplex ℤ X N).X 1} :
-- imply
  f = 0 ↔ ∀ σ : Sing 1 X, cochainEvalN X N 1 f σ = 0 := by
-- proof
  apply SingularCohomology.cochain1_eq_zero_iff X N f


-- created on 2026-10-23
