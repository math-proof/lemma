import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.LieGroups.code.FrobeniusReciprocity


/--
[verma_hom_backward_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/FrobeniusReciprocity.lean)
-/
@[path]
private lemma verma_hom_backward_spec
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {W : Type u}
  [AddCommGroup W]
  [Module R W]
  [LieRingModule 𝔤 W]
  [LieModule R 𝔤 W]
  {w : singularVectorsOfWeight Δ W wt}
-- given
  (hV : IsVermaModule Δ M wt) :
-- imply
  (verma_hom_backward hV w) hV.highestWeightVec = w.val :=
-- proof
  (hV.universal_map W w.val w.prop.1 w.prop.2).choose_spec

/--
[verma_hom_forward_backward](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/FrobeniusReciprocity.lean)
-/
@[path]
private lemma verma_hom_forward_backward
  {R : Type u}
  [CommRing R]
  {𝔤 : Type u}
  [LieRing 𝔤]
  [LieAlgebra R 𝔤]
  {Δ : TriangularDecomposition R 𝔤}
  {M : Type u}
  [AddCommGroup M]
  [Module R M]
  [LieRingModule 𝔤 M]
  [LieModule R 𝔤 M]
  {wt : Δ.𝔥 →ₗ[R] R}
  {W : Type u}
  [AddCommGroup W]
  [Module R W]
  [LieRingModule 𝔤 W]
  [LieModule R 𝔤 W]
  {w : singularVectorsOfWeight Δ W wt}
-- given
  (hV : IsVermaModule Δ M wt) :
-- imply
  verma_hom_forward hV (verma_hom_backward hV w) = w := by
-- proof
  ext
  exact verma_hom_backward_spec hV w


-- created on 2026-10-23
-- updated on 2026-10-24
