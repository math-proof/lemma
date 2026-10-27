import Mathlib
import Initialize.Tactic.Attr.Basic
import Instance.v1.Atlas.AlgebraicTopologyI.code.Section37.Part3
open CategoryTheory TopologicalSpace Limits PoincareDuality PoincareDuality.CombinedOpenNhds
open Limits TopologicalSpace
open PoincareDuality
open CategoryTheory PoincareDuality
open CategoryTheory AlgebraicTopology LinearMap SingularCohomology
open AlgebraicTopologyI PoincareDuality


namespace PoincareDuality

/--
[fiveLemma_moduleCat_isIso](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean)
-/
@[path]
lemma fiveLemma_moduleCat_isIso
  {R : Type}
  [CommRing R]
  {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : ModuleCat.{0} R}
  {f₁ : A₁ ⟶ A₂}
  {f₂ : A₂ ⟶ A₃}
  {f₃ : A₃ ⟶ A₄}
  {f₄ : A₄ ⟶ A₅}
  {g₁ : B₁ ⟶ B₂}
  {g₂ : B₂ ⟶ B₃}
  {g₃ : B₃ ⟶ B₄}
  {g₄ : B₄ ⟶ B₅}
  {α : A₁ ⟶ B₁}
  {β : A₂ ⟶ B₂}
  {γ : A₃ ⟶ B₃}
  {δ : A₄ ⟶ B₄}
  {ε : A₅ ⟶ B₅}
-- given
  (sq₁ : f₁ ≫ β = α ≫ g₁)
  (sq₂ : f₂ ≫ γ = β ≫ g₂)
  (sq₃ : f₃ ≫ δ = γ ≫ g₃)
  (sq₄ : f₄ ≫ ε = δ ≫ g₄)
  (hexTopExact : (ComposableArrows.mk₄ f₁ f₂ f₃ f₄).Exact)
  (hexBotExact : (ComposableArrows.mk₄ g₁ g₂ g₃ g₄).Exact)
  (hα : Epi α)
  (hβ : IsIso β)
  (hδ : IsIso δ)
  (hε : Mono ε) :
-- imply
  IsIso γ :=
-- proof
  Abelian.isIso_of_epi_of_isIso_of_isIso_of_mono hexTopExact hexBotExact
    (ComposableArrows.homMk₄ α β γ δ ε sq₁ sq₂ sq₃ sq₄) hα hβ hδ hε

end PoincareDuality

/--
[toNhdsInter_monotone](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean)
-/
@[path]
private lemma toNhdsInter_monotone_eq
  {α : Type u}
  [TopologicalSpace α]
  {A : ℕ → Set α}
-- given
  (hA : Antitone A) :
-- imply
  Monotone (toNhdsInter hA) := by
-- proof
  apply PoincareDuality.CombinedOpenNhds.toNhdsInter_monotone hA

/--
[toNhdsInter_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean)
-/
@[path]
private lemma toNhdsInter_cofinal_eq
  {α : Type u}
  [TopologicalSpace α]
  {A : ℕ → Set α}
  [T2Space α]
-- given
  (hA : Antitone A)
  (hcpt : ∀ k, IsCompact (A k)) :
-- imply
  ∀ (V : OpenNhdsOfSet (⋂ k, A k)), ∃ (p : CombinedOpenNhds A), V ≤ toNhdsInter hA p := by
-- proof
  apply PoincareDuality.CombinedOpenNhds.toNhdsInter_cofinal hA hcpt

/--
[toNhdsInter_functor_final](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section37.lean)
-/
@[path]
private lemma toNhdsInter_functor_final_eq
  {α : Type u}
  [TopologicalSpace α]
  {A : ℕ → Set α}
  [T2Space α]
-- given
  (hA : Antitone A)
  (hcpt : ∀ k, IsCompact (A k)) :
-- imply
  letI : IsDirected (CombinedOpenNhds A) (· ≤ ·) := isDirectedOfAntitone hA (toNhdsInter_monotone hA).functor.Final := by
-- proof
  apply PoincareDuality.CombinedOpenNhds.toNhdsInter_functor_final hA hcpt


-- created on 2026-10-23
