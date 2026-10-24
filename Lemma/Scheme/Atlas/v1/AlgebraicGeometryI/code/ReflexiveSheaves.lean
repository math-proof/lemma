import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.ReflexiveSheaves
open ReflexiveSheaf
open Module


namespace ReflexiveSheaf

/--
[isReflexive_iff_eval_bijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean)
-/
@[path]
lemma isReflexive_iff_eval_bijective
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M] :
-- imply
  IsReflexive R M ↔ Function.Bijective (Dual.eval R M) :=
-- proof
  ⟨fun h => h.bijective_dual_eval', fun h => ⟨h⟩⟩

end ReflexiveSheaf

namespace ReflexiveSheaf

/--
[eval_apply_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean)
-/
@[path]
lemma eval_apply_eq
  [CommSemiring R]
  [AddCommMonoid M]
  [Module R M]
  {m : M}
  {φ : Dual R M} :
-- imply
  doubleDualMap R M m φ = φ m :=
-- proof
  rfl

end ReflexiveSheaf

namespace ReflexiveSheaf

/--
[locallyFree_isReflexive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/ReflexiveSheaves.lean)
-/
@[path]
lemma locallyFree_isReflexive
  [CommRing R]
  {M : Type*}
  [AddCommGroup M]
  [Module R M]
  [Module.Finite R M]
  [Module.Projective R M] :
-- imply
  IsReflexive R M :=
-- proof
  Module.instIsReflexiveOfFiniteOfProjective R M

end ReflexiveSheaf


-- created on 2026-10-23
