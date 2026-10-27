import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.TateCohomology
open CategoryTheory groupCohomology


/-- ported from external source -/
@[path]
private lemma main
  [CommRing k] [Group G]
  {A : Rep k G}
  {n : ℕ} :
-- imply
  Function.Bijective (groupCohomology.map (⊤ : Subgroup G).subtype (𝟙 (Rep.res (⊤ : Subgroup G).subtype A)) n).hom := by
  classical
    set T : Subgroup G := ⊤ with hT
    have hlev : ∀ i, IsIso ((cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))).f i) := by
-- proof
      intro i
      rw [cochainsMap_f]
      apply (ConcreteCategory.isIso_iff_bijective _).2
      simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp]
      refine Function.Bijective.comp ?_ ?_
      ·
        refine ⟨fun v w h => ?_, fun u => ⟨u, rfl⟩⟩
        exact h
      ·
        refine ⟨fun v w h => ?_, fun u => ?_⟩
        ·
          funext z
          have := congrFun h (fun j => ⟨z j, by rw [hT]; trivial⟩)
          simp [LinearMap.funLeft_apply] at this
          exact this
        ·
          refine ⟨fun z => u (fun j => ⟨z j, by rw [hT]; trivial⟩), ?_⟩
          funext y
          simp only [LinearMap.funLeft_apply, Function.comp_def, Subgroup.coe_subtype, Subtype.coe_eta]
    have : IsIso (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) := HomologicalComplex.Hom.isIso_of_components _
    have : IsIso (HomologicalComplex.homologyMap (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) n) := inferInstance
    exact ConcreteCategory.bijective_of_isIso (HomologicalComplex.homologyMap (cochainsMap T.subtype (𝟙 (Rep.res T.subtype A))) n)


-- created on 2026-10-23
