import Mathlib
import sympy.Basic
import Def.v1.Atlas.LieGroups.code.Lemma23_4


/--
[form_posRoot_pos_of_WeightBilinForm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/Lemma23_4.lean)
-/
@[path]
lemma form_posRoot_pos_of_WeightBilinForm
  {R : Type u}
  [CommRing R]
  {Δ : TriangularDecomposition R 𝔤}
  {rd : PositiveRootData Δ}
  {wg : WeylGroupData Δ}
  [LinearOrder R]
  [IsStrictOrderedRing R]
  {B : WeightBilinForm wg}
  {alpha : Δ.𝔥 →ₗ[R] R}
-- given
  (halpha_pos : alpha ∈ rd.posRoots) :
-- imply
  (0 : R) < B.form alpha alpha :=
-- proof
  B.form_posRoot_pos rd alpha halpha_pos


-- created on 2026-10-24
