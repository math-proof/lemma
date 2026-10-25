import Mathlib
import sympy.Basic
import Def.v1.Atlas.ArithmeticGeometry.code.CotangentLocal.Part3
open IsLocalRing CotangentDual


namespace CotangentDual

/--
[cotangent_dual_tangent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
lemma cotangent_dual_tangent
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  Nonempty (Module.Dual k (CotangentSpace R) ≃ₗ[k] Derivation k R k) :=
-- proof
  ⟨cotangentDualEquivDerivation hφ⟩

end CotangentDual

/--
[algebraMap_comp_section](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma algebraMap_comp_section_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {c : k} :
-- imply
  algebraMap R k (algebraMap k R c) = c := by
-- proof
  apply CotangentDual.algebraMap_comp_section c

/--
[mem_maximalIdeal_map_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma mem_maximalIdeal_map_zero_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {x : maximalIdeal R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  algebraMap R k x.val = 0 := by
-- proof
  apply CotangentDual.mem_maximalIdeal_map_zero hφ x

/--
[projMaxIdeal_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma projMaxIdeal_add_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {x y : R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  projMaxIdeal hφ (x + y) = projMaxIdeal hφ x + projMaxIdeal hφ y := by
-- proof
  apply CotangentDual.projMaxIdeal_add hφ x y

/--
[projMaxIdeal_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma projMaxIdeal_smul_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {c : k}
  {x : R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  projMaxIdeal hφ (c • x) = c • projMaxIdeal hφ x := by
-- proof
  apply CotangentDual.projMaxIdeal_smul hφ c x

/--
[projMaxIdeal_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma projMaxIdeal_one_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  projMaxIdeal hφ 1 = 0 := by
-- proof
  apply CotangentDual.projMaxIdeal_one hφ

/--
[projMaxIdeal_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma projMaxIdeal_of_mem_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {m : maximalIdeal R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  (maximalIdeal R).toCotangent (projMaxIdeal hφ m.val) = (maximalIdeal R).toCotangent m := by
-- proof
  apply CotangentDual.projMaxIdeal_of_mem hφ m

/--
[projCotangent_leibniz](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma projCotangent_leibniz_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {x y : R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  (maximalIdeal R).toCotangent (projMaxIdeal hφ (x * y)) = algebraMap k R (algebraMap R k x) • (maximalIdeal R).toCotangent (projMaxIdeal hφ y) + algebraMap k R (algebraMap R k y) • (maximalIdeal R).toCotangent (projMaxIdeal hφ x) := by
-- proof
  apply CotangentDual.projCotangent_leibniz hφ x y

/--
[derivRestrict_vanishes](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CotangentLocal.lean)
-/
@[path]
private lemma derivRestrict_vanishes_eq
  [CommRing R]
  [IsLocalRing R]
  [Field k]
  [Algebra k R]
  [Algebra R k]
  [IsScalarTower k R k]
  {D : Derivation k R k}
  {x y : maximalIdeal R}
-- given
  (hφ : Function.Surjective (algebraMap R k)) :
-- imply
  derivRestrict D (x * y) = 0 := by
-- proof
  apply CotangentDual.derivRestrict_vanishes hφ D x y


-- created on 2026-10-23
