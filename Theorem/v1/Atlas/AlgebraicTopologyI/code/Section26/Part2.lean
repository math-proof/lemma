/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section26.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.CupProductHelpers
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.AlgebraicTopology.SimplicialSet.TopAdj
import Mathlib.CategoryTheory.Abelian.Ext
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexLimits
import Mathlib.RingTheory.Coalgebra.Basic
import Mathlib.RingTheory.PrincipalIdealDomain
import Mathlib.LinearAlgebra.FreeModule.Basic
import Mathlib.LinearAlgebra.DirectSum.TensorProduct
import Mathlib.LinearAlgebra.TensorProduct.Graded.External
import Mathlib.LinearAlgebra.TensorProduct.RightExactness
import Def.v1.Atlas.AlgebraicTopologyI.code.Section26.Part5
open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct

open CategoryTheory AlgebraicTopology Limits AlgebraicTopologyI MonoidalCategory
open scoped TensorProduct
open SingularCohomology


namespace SingularCohomology

open scoped Simplicial

open Opposite SimplexCategory

section

set_option backward.isDefEq.respectTransparency false

set_option maxHeartbeats 800000

/-- Identifying a face of `σ` with a point of `X` agrees with evaluating
the underlying continuous map at the corresponding vertex of `Δ^1`. -/
lemma sing0EquivX_face_eq (X : TopCat.{0}) (i : Fin 2) (σ : Sing 1 X) :
    sing0EquivX X ((TopCat.toSSet.obj X).map (SimplexCategory.δ i).op σ) =
    (TopCat.toSSetObjEquiv X (op ⦋1⦌) σ).1
      (_root_.stdSimplex.map (SimplexCategory.δ i).toOrderHom default) := by
  rfl

/-- The image of the standard `0`-simplex under `δ_1 : Δ^0 → Δ^1` is the
first standard basis point `e₀`. -/
lemma stdSimplex_map_δ1_default :
    (_root_.stdSimplex.map (SimplexCategory.δ (1 : Fin 2)).toOrderHom
      (default : stdSimplex ℝ (Fin 1))) =
    ⟨Pi.single 0 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
  rw [Subsingleton.elim default (_root_.stdSimplex.vertex 0),
    _root_.stdSimplex.map_vertex]
  simp [SimplexCategory.δ, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb,
    Fin.succAbove, _root_.stdSimplex.vertex]

/-- The image of the standard `0`-simplex under `δ_0 : Δ^0 → Δ^1` is the
second standard basis point `e₁`. -/
lemma stdSimplex_map_δ0_default :
    (_root_.stdSimplex.map (SimplexCategory.δ (0 : Fin 2)).toOrderHom
      (default : stdSimplex ℝ (Fin 1))) =
    ⟨Pi.single 1 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
  rw [Subsingleton.elim default (_root_.stdSimplex.vertex 0),
    _root_.stdSimplex.map_vertex]
  simp [SimplexCategory.δ, mkHom, Hom.toOrderHom_mk, Fin.succAboveOrderEmb,
    Fin.succAbove, _root_.stdSimplex.vertex]

/-- Any singular `1`-simplex `σ` realises a path joining its two faces. -/
lemma joined_of_one_simplex (X : TopCat.{0}) (σ : Sing 1 X) :
    Joined (sing0EquivX X (face₁ X σ)) (sing0EquivX X (face₀ X σ)) := by
  set f := TopCat.toSSetObjEquiv X (op ⦋1⦌) σ
  rw [face₁, sing0EquivX_face_eq, face₀, sing0EquivX_face_eq]
  rw [stdSimplex_map_δ1_default, stdSimplex_map_δ0_default]
  have h0 : stdSimplexHomeomorphUnitInterval.symm (0 : unitInterval) =
      ⟨Pi.single 0 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
    rw [← stdSimplexHomeomorphUnitInterval_zero, Homeomorph.symm_apply_apply]
  have h1 : stdSimplexHomeomorphUnitInterval.symm (1 : unitInterval) =
      ⟨Pi.single 1 (1 : ℝ), single_mem_stdSimplex _ _⟩ := by
    rw [← stdSimplexHomeomorphUnitInterval_one, Homeomorph.symm_apply_apply]
  let g : C(unitInterval, stdSimplex ℝ (Fin 2)) :=
    ⟨stdSimplexHomeomorphUnitInterval.symm, stdSimplexHomeomorphUnitInterval.symm.continuous⟩
  refine ⟨⟨f.comp g, ?_, ?_⟩⟩
  · show f (g 0) = f ⟨Pi.single 0 1, single_mem_stdSimplex _ _⟩
    simp only [g, ContinuousMap.coe_mk, h0]
  · show f (g 1) = f ⟨Pi.single 1 1, single_mem_stdSimplex _ _⟩
    simp only [g, ContinuousMap.coe_mk, h1]

end
end SingularCohomology
