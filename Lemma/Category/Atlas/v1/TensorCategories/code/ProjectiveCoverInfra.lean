import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.ProjectiveCoverInfra.Part4
open CategoryTheory MonoidalCategory Category Limits ProjectiveCoverInfra


/--
[postcomp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma postcomp_apply_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P : C}
  {Y Z : C}
  {f : Y ⟶ Z}
-- given
  (h : P ⟶ Y) :
-- imply
  postcomp 𝕜 P f h = h ≫ f := by
-- proof
  apply ProjectiveCoverInfra.postcomp_apply 𝕜 P f h

/--
[precomp_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precomp_apply_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P : C}
  {a : P ⟶ P}
  {X : C}
-- given
  (h : P ⟶ X) :
-- imply
  precomp 𝕜 P a X h = a ≫ h := by
-- proof
  apply ProjectiveCoverInfra.precomp_apply 𝕜 P a X h

/--
[homScalar_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma homScalar_spec_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
  {f : P ⟶ S}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  f = homScalar 𝕜 hdim π hπ f • π := by
-- proof
  apply ProjectiveCoverInfra.homScalar_spec 𝕜 hdim π hπ f

/--
[smul_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma smul__eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
  {c d : 𝕜}
-- given
  (hπ : π ≠ 0)
  (h : c • π = d • π) :
-- imply
  c = d := by
-- proof
  apply ProjectiveCoverInfra.smul_ 𝕜 π hπ h

/--
[precompScalar_spec](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precompScalar_spec_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
  {a : End P}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  a ≫ π = precompScalar 𝕜 hdim π hπ a • π := by
-- proof
  apply ProjectiveCoverInfra.precompScalar_spec 𝕜 hdim π hπ a

/--
[precompScalar_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precompScalar_mul_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
  {a b : End P}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  precompScalar 𝕜 hdim π hπ (a * b) = precompScalar 𝕜 hdim π hπ a * precompScalar 𝕜 hdim π hπ b := by
-- proof
  apply ProjectiveCoverInfra.precompScalar_mul 𝕜 hdim π hπ a b

/--
[precompScalar_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precompScalar_add_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
  {a b : End P}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  precompScalar 𝕜 hdim π hπ (a + b) = precompScalar 𝕜 hdim π hπ a + precompScalar 𝕜 hdim π hπ b := by
-- proof
  apply ProjectiveCoverInfra.precompScalar_add 𝕜 hdim π hπ a b

/--
[precompScalar_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precompScalar_one_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  precompScalar 𝕜 hdim π hπ (1 : End P) = 1 := by
-- proof
  apply ProjectiveCoverInfra.precompScalar_one 𝕜 hdim π hπ

/--
[precompScalar_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/ProjectiveCoverInfra.lean)
-/
@[path]
private lemma precompScalar_zero_eq
  {𝕜 : Type w}
  [Field 𝕜]
  {C : Type u}
  [Category.{v} C]
  [Preadditive C]
  [Linear 𝕜 C]
  {P S : C}
  {π : P ⟶ S}
-- given
  (hdim : Module.finrank 𝕜 (P ⟶ S) = 1)
  (hπ : π ≠ 0) :
-- imply
  precompScalar 𝕜 hdim π hπ (0 : End P) = 0 := by
-- proof
  apply ProjectiveCoverInfra.precompScalar_zero 𝕜 hdim π hπ


-- created on 2026-10-23
