import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.TensorCategories.code.BasedRings
import Lemma.Category.Atlas.v1.TensorCategories.code.BasedRings


/--
[Proposition_1_42_9](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/Proposition_1_42_9.lean)
-/
@[path]
lemma Proposition_1_42_9
  {G : Type*}
  [DecidableEq G]
  [Fintype G]
  [Group G]
  {k : Type*}
  [Field k] :
-- imply
  (∀ (ω : NormalizedGroupCocycle3 G kˣ), (∀ g h : G, (CG.tensorObj' (⟨g⟩ : CG G kˣ ω) (⟨h⟩ : CG G kˣ ω)).val = g * h) ∧ (CG.unit' : CG G kˣ ω).val = (1 : G) ∧ (∀ g : G, (CG.dualObj (⟨g⟩ : CG G kˣ ω)).val = (FusionRing.groupRingFusionRing G).star g)) ∧ (∀ (categ : Categorification (FusionRing.groupRingFusionRing G) k), ∃ (ω : NormalizedGroupCocycle3 G kˣ), Nonempty (@MonoidalEquiv categ.C categ.cat categ.monoidal (CG G kˣ ω) _ inferInstance)) ∧ (∀ (ω₁ ω₂ : NormalizedGroupCocycle3 G kˣ), CocycleOutOrbitEquiv ω₁ ω₂ ↔ Nonempty (MonoidalEquiv (CG G kˣ ω₁) (CG G kˣ ω₂))) :=
-- proof
  ⟨fun ω => Proposition_1_42_9_VecGomega_is_categorification G k ω,
    fun categ => Proposition_1_42_9_categorifications_are_VecGomega G k categ,
    fun ω₁ ω₂ => Proposition_1_42_9_parametrization G k ω₁ ω₂⟩


-- created on 2026-10-23
