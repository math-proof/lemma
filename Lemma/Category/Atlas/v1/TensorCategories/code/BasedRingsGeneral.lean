import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.TensorCategories.code.BasedRingsGeneral
open CategoryTheory MonoidalCategory Finset CategoricalMultitensorData


namespace CategoricalMultitensorData

/--
[proposition_1_42_4_based](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRingsGeneral.lean)
-/
@[path]
lemma proposition_1_42_4_based
  [Field κ]
  {C : Type u}
  [Category.{v} C] :
-- imply
  ∃ (B : BasedRing cmd.ι), B.N = cmd.N ∧ B.I₀ = cmd.I₀ ∧ B.star = cmd.star :=
-- proof
  ⟨toBasedRing, rfl, rfl, rfl⟩

end CategoricalMultitensorData

namespace CategoricalMultitensorData

/--
[proposition_1_42_4_unital](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRingsGeneral.lean)
-/
@[path]
lemma proposition_1_42_4_unital
  [Field κ]
  {C : Type u}
  [Category.{v} C]
-- given
  (hunit : ∃ u, cmd.I₀ = {u}) :
-- imply
  ∃ (B : UnitalBasedRing cmd.ι), B.N = cmd.N ∧ B.I₀ = cmd.I₀ ∧ B.star = cmd.star := by
-- proof
  obtain ⟨u, hu⟩ := hunit
  exact ⟨⟨toBasedRing, u, hu⟩, rfl, rfl, rfl⟩

end CategoricalMultitensorData

namespace CategoricalMultitensorData

/--
[proposition_1_42_4_multifusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRingsGeneral.lean)
-/
@[path]
lemma proposition_1_42_4_multifusion
  [Field κ]
  {C : Type u}
  [Category.{v} C] :
-- imply
  ∃ (B : BasedRing cmd.ι), B.N = cmd.N ∧ B.I₀ = cmd.I₀ ∧ B.star = cmd.star :=
-- proof
  ⟨toBasedRing, rfl, rfl, rfl⟩

end CategoricalMultitensorData

namespace CategoricalMultitensorData

/--
[proposition_1_42_4_fusion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/BasedRingsGeneral.lean)
-/
@[path]
lemma proposition_1_42_4_fusion
  [Field κ]
  {C : Type u}
  [Category.{v} C]
-- given
  (hunit : ∃ u, cmd.I₀ = {u}) :
-- imply
  ∃ (B : UnitalBasedRing cmd.ι), B.N = cmd.N ∧ B.I₀ = cmd.I₀ ∧ B.star = cmd.star := by
-- proof
  obtain ⟨u, hu⟩ := hunit
  exact ⟨⟨toBasedRing, u, hu⟩, rfl, rfl, rfl⟩

end CategoricalMultitensorData


-- created on 2026-10-23
