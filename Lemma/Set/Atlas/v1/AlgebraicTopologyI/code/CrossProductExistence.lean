import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.CrossProductExistence
open Finset BigOperators AlgebraicTopologyI
open ContinuousMap


namespace AlgebraicTopologyI

/--
[SingularChains.map_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma SingularChains.map_comp
  {n : ℕ}
  {X Y Z : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  [TopologicalSpace Z]
  {f : C(Y, Z)}
  {g : C(X, Y)}
  {s : SingularChains n X} :
-- imply
  SingularChains.map (f.comp g) s = SingularChains.map f (SingularChains.map g s) := by
-- proof
  show (FreeAbelianGroup.map (SingularSimplex.map (f.comp g))) s =
    (FreeAbelianGroup.map (SingularSimplex.map f)) ((FreeAbelianGroup.map (SingularSimplex.map g)) s)
  rw [← FreeAbelianGroup.map_comp_apply]
  congr 1

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[boundaryMap_map_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma boundaryMap_map_comm
  {n : ℕ}
  {X Y : Type}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : C(X, Y)}
  {s : SingularChains (n + 1) X} :
-- imply
  boundaryMap n Y (SingularChains.map f s) = SingularChains.map f (boundaryMap n X s) := by
-- proof
  have h_eq : (boundaryMap n Y).comp (SingularChains.map f) =
    (SingularChains.map f).comp (boundaryMap n X) := by
    apply FreeAbelianGroup.lift_ext
    intro sigma
    show (boundaryMap n Y) (FreeAbelianGroup.of (SingularSimplex.map f sigma)) =
      (SingularChains.map f) ((boundaryMap n X) (FreeAbelianGroup.of sigma))
    unfold boundaryMap SingularChains.map SingularSimplex.map SingularSimplex.face
    erw [FreeAbelianGroup.lift_apply_of, FreeAbelianGroup.lift_apply_of, map_sum]
    congr 1
    ext i : 1
    erw [map_zsmul, FreeAbelianGroup.map_of_apply]
    simp only [ContinuousMap.comp_assoc]
    rfl
  exact DFunLike.congr_fun h_eq s

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[iotaSimplex_face0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma iotaSimplex_face0
-- imply
  SingularSimplex.face 0 iotaSimplex = constSimplex ⟨1, unitInterval.one_mem⟩ := by
-- proof
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  obtain ⟨_, hsum⟩ := t.2
  rw [Fin.sum_univ_one] at hsum
  simpa using hsum

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[iotaSimplex_face1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma iotaSimplex_face1
-- imply
  SingularSimplex.face 1 iotaSimplex = constSimplex ⟨0, unitInterval.zero_mem⟩ := by
-- proof
  apply ContinuousMap.ext
  intro t
  simp only [SingularSimplex.face, iotaSimplex, faceInclusion, constSimplex,
    ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.const_apply]
  apply Subtype.ext
  simp

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[boundary_iota](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma boundary_iota
-- imply
  boundaryMap 0 ↥I (FreeAbelianGroup.of iotaSimplex) = constChain ⟨1, unitInterval.one_mem⟩ - constChain ⟨0, unitInterval.zero_mem⟩ := by
-- proof
  unfold boundaryMap
  erw [FreeAbelianGroup.lift_apply_of]
  rw [Fin.sum_univ_two]
  simp only [Fin.val_zero, pow_zero, one_smul, Fin.val_one, pow_one, neg_one_smul,
    iotaSimplex_face0, iotaSimplex_face1, constChain]
  abel

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[inclusionLeft_one_eq_inclusion1](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma inclusionLeft_one_eq_inclusion1
  {X : Type}
  [TopologicalSpace X] :
-- imply
  inclusionLeft (Y := ↥I) ⟨1, unitInterval.one_mem⟩ = inclusion1 X := by
-- proof
  apply ContinuousMap.ext; intro x; rfl

end AlgebraicTopologyI

namespace AlgebraicTopologyI

/--
[inclusionLeft_zero_eq_inclusion0](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/CrossProductExistence.lean)
-/
@[path]
lemma inclusionLeft_zero_eq_inclusion0
  {X : Type}
  [TopologicalSpace X] :
-- imply
  inclusionLeft (Y := ↥I) ⟨0, unitInterval.zero_mem⟩ = inclusion0 X := by
-- proof
  apply ContinuousMap.ext; intro x; rfl
/-- Existence of a natural chain homotopy between the two inclusions
`X → X × I`. The witness is built by crossing with the fundamental
`1`-simplex `ι₁` on `I` and using the Leibniz rule and normalization of
the singular chain cross product. This is the chain-level engine behind
Theorem 6.1. -/
end



-- created on 2026-10-23
