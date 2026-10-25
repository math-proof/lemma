import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section28
open SimplexCategory CategoryTheory ProductsInCohomology


namespace ProductsInCohomology

/--
[frontProjection_frontProjection_reassoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section28.lean)
-/
@[path]
lemma frontProjection_frontProjection_reassoc
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {p q r : ℕ}
  {σ : C(↥(stdSimplex ℝ (Fin (p + q + r + 1))), X × Y × Z)} :
-- imply
  frontProjection p q (frontProjection (p + q) r (reassocSimplex _ σ)) = frontProjection p (q + r) (castSimplex _ _ (by omega) σ) := by
-- proof
  ext ⟨x, hx⟩
  simp only [frontProjection, reassocSimplex, castSimplex, frontFaceMap, frontFace,
    ContinuousMap.coe_mk, ContinuousMap.comp_apply, stdSimplex.map_comp_apply]
  congr 1

end ProductsInCohomology

namespace ProductsInCohomology

/--
[backProjection_frontProjection_reassoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section28.lean)
-/
@[path]
lemma backProjection_frontProjection_reassoc
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {p q r : ℕ}
  {σ : C(↥(stdSimplex ℝ (Fin (p + q + r + 1))), X × Y × Z)} :
-- imply
  backProjection p q (frontProjection (p + q) r (reassocSimplex _ σ)) = frontProjection q r (backProjection p (q + r) (castSimplex _ _ (by omega) σ)) := by
-- proof
  ext ⟨x, hx⟩
  simp only [frontProjection, backProjection, reassocSimplex, castSimplex,
    frontFaceMap, backFaceMap, frontFace, backFace,
    ContinuousMap.coe_mk, ContinuousMap.comp_apply, stdSimplex.map_comp_apply]
  congr 1

end ProductsInCohomology

namespace ProductsInCohomology

/--
[backProjection_reassoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section28.lean)
-/
@[path]
lemma backProjection_reassoc
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {p q r : ℕ}
  {σ : C(↥(stdSimplex ℝ (Fin (p + q + r + 1))), X × Y × Z)} :
-- imply
  backProjection (p + q) r (reassocSimplex _ σ) = backProjection q r (backProjection p (q + r) (castSimplex _ _ (by omega) σ)) := by
-- proof
  ext ⟨x, hx⟩
  simp only [backProjection, reassocSimplex, castSimplex, backFaceMap, backFace,
    ContinuousMap.coe_mk, ContinuousMap.comp_apply, stdSimplex.map_comp_apply]
  dsimp [Homeomorph.prodAssoc, Equiv.prodAssoc]
  congr 1; congr 1; congr 1
  ext ⟨k, hk⟩; congr 2
  ext ⟨j, hj⟩
  show j + (p + q) = j + q + p
  omega

end ProductsInCohomology

namespace ProductsInCohomology

/--
[cochainCrossProduct_assoc](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section28.lean)
-/
@[path]
lemma cochainCrossProduct_assoc
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  [CommRing R]
  {p q r : ℕ}
  {f : C(↥(stdSimplex ℝ (Fin (p + 1))), X) → R}
  {g : C(↥(stdSimplex ℝ (Fin (q + 1))), Y) → R}
  {σ : C(↥(stdSimplex ℝ (Fin (p + q + r + 1))), X × Y × Z)}
-- given
  (h : C(↥(stdSimplex ℝ (Fin (r + 1))), Z) → R) :
-- imply
  cochainCrossProduct (p + q) r (cochainCrossProduct p q f g) h (reassocSimplex _ σ) = cochainCrossProduct p (q + r) f (cochainCrossProduct q r g h) (castSimplex _ _ (by omega) σ) := by
-- proof
  simp only [cochainCrossProduct]
  rw [frontProjection_frontProjection_reassoc, backProjection_frontProjection_reassoc,
    backProjection_reassoc]
  ring

end ProductsInCohomology


-- created on 2026-10-23
