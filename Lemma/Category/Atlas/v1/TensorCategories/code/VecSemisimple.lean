import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.TensorCategories.code.VecSemisimple.Part2
open CategoryTheory MonoidalCategory Limits Module VecSemisimple


/--
[nontrivial_of_not_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean)
-/
@[path]
private lemma nontrivial_of_not_isZero_eq
  {k : Type u}
  [Field k]
  {X : FGModuleCat.{u} k}
-- given
  (h : ¬ IsZero X) :
-- imply
  Nontrivial X := by
-- proof
  apply VecSemisimple.nontrivial_of_not_isZero k X h

/--
[ofHom_toSpanSingleton_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean)
-/
@[path]
private lemma ofHom_toSpanSingleton_ne_zero_eq
  {k : Type u}
  [Field k]
  {X : FGModuleCat.{u} k}
  {v : X}
-- given
  (hv : v ≠ 0) :
-- imply
  FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) ≠ (0 : FGModuleCat.of k k ⟶ X) := by
-- proof
  apply VecSemisimple.ofHom_toSpanSingleton_ne_zero k X v hv

/--
[mono_ofHom_toSpanSingleton](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/VecSemisimple.lean)
-/
@[path]
private lemma mono_ofHom_toSpanSingleton_eq
  {k : Type u}
  [Field k]
  {X : FGModuleCat.{u} k}
  {v : X}
-- given
  (hv : v ≠ 0) :
-- imply
  Mono (FGModuleCat.ofHom (LinearMap.toSpanSingleton k (↑X) v) : FGModuleCat.of k k ⟶ X) := by
-- proof
  apply VecSemisimple.mono_ofHom_toSpanSingleton k X v hv


-- created on 2026-10-23
