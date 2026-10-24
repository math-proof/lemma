import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_GroupCohomology_ContinuousH2
import Lemma.Definitions.Def_GroupCohomology_ContinuousH1
import Lemma.Definitions.Def_GroupCohomology_CupProduct
import Lemma.Int.P2MUtil
open CategoryTheory groupCohomology
open Int


namespace Definitions
end Definitions

/--
[groupCohomology_cup20_deltaCochain1_sub_cup_deltaCochain0_mem_levelCoboundaries2](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cup20_deltaCochain1_sub_cup_deltaCochain0_mem_levelCoboundaries2.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {r : G →* (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)}
  {M' M M'' D'' D D' N : Rep.{u} k G}
  {i : M' ⟶ M}
  {π : M ⟶ M''}
  {πD : D'' ⟶ D}
  {iD : D ⟶ D'}
  {φ' : M' →ₗ[k] D' →ₗ[k] N}
  {φ : M →ₗ[k] D →ₗ[k] N}
  {φ'' : M'' →ₗ[k] D'' →ₗ[k] N}
  {c : cocycles₁ M''}
  {y : D'}
-- given
  (hπ : Function.Surjective π.hom)
  (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
  (hiD : Function.Surjective iD.hom)
  (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
  (hφ : Rep.IsEquivariantBilinear M D N φ)
  (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
  (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
  (hsmD : ∀ x : D, ∃ F : IntermediateField ℚ (AlgebraicClosure ℚ), FiniteDimensional ℚ F ∧ ∀ s, r s ∈ F.fixingSubgroup → D.ρ s x = x)
  (hc : IsLevelConstant₁ r (⇑c))
  (hy : ∀ s, D'.ρ s y = y) :
-- imply
  ((fun st : G × G => φ' (deltaCochain₁ i π hπ (⇑c) st) (D'.ρ (st.1 * st.2) y))
        - cupCochain φ'' (⇑c) (deltaCochain₀ πD iD hiD y))
      ∈ levelCoboundaries₂ r N := by
-- proof
  set ct : G → M := Function.surjInv hπ ∘ (⇑c) with hct
  set yt : D := Function.surjInv hiD y with hyt
  have hπct : ∀ g, π.hom (ct g) = c g := fun g => Function.surjInv_eq hπ (c g)
  have hiDyt : iD.hom yt = y := Function.surjInv_eq hiD y
  have hδ1 : ∀ s t, i.hom (deltaCochain₁ i π hπ (⇑c) (s, t)) = M.ρ s (ct t) - ct (s * t) + ct s := by
    intro s t
    rw [deltaCochain₁_apply]
    refine apply_preimageFun i ((hex _).1 ?_)
    rw [map_add, map_sub, Rep.hom_comm_apply]
    change M''.ρ s (π.hom (ct t)) - π.hom (ct (s * t)) + π.hom (ct s) = 0
    rw [hπct, hπct, hπct, (mem_cocycles₁_iff (⇑c)).1 c.2 s t]
    abel
  have hδ0 : ∀ t, πD.hom (deltaCochain₀ πD iD hiD y t) = D.ρ t yt - yt := by
    intro t
    rw [deltaCochain₀_apply]
    refine apply_preimageFun πD ((hexD _).1 ?_)
    rw [map_sub, Rep.hom_comm_apply, hiDyt, hy t, sub_self]
  refine (mem_levelCoboundaries₂_iff r N _).2 ⟨fun s => φ (ct s) (D.ρ s yt), ?_, ?_⟩
  ·
    obtain ⟨F₁, hF₁, h₁⟩ := hc
    obtain ⟨F₂, hF₂, h₂⟩ := hsmD yt
    have : FiniteDimensional ℚ F₁ := hF₁
    have : FiniteDimensional ℚ F₂ := hF₂
    refine ⟨F₁ ⊔ F₂, inferInstance, fun g s hs => ?_⟩
    show φ (ct (g * s)) (D.ρ (g * s) yt) = φ (ct g) (D.ρ g yt)
    rw [hct, Function.comp_apply, Function.comp_apply,
      h₁ g s (IntermediateField.fixingSubgroup_antitone le_sup_left hs), map_mul, Module.End.mul_apply,
      h₂ s (IntermediateField.fixingSubgroup_antitone le_sup_right hs)]
  ·
    funext ⟨s, t⟩
    rw [d₁₂_hom_apply, Pi.sub_apply, cupCochain_apply]
    change N.ρ s (φ (ct t) (D.ρ t yt)) - φ (ct (s * t)) (D.ρ (s * t) yt) + φ (ct s) (D.ρ s yt) =
      φ' (deltaCochain₁ i π hπ (⇑c) (s, t)) (D'.ρ (s * t) y) -
        φ'' (c s) (D''.ρ s (deltaCochain₀ πD iD hiD y t))
    have h1 : φ' (deltaCochain₁ i π hπ (⇑c) (s, t)) (D'.ρ (s * t) y) =
        φ (M.ρ s (ct t) - ct (s * t) + ct s) (D.ρ (s * t) yt) := by
      rw [← hδ1, hcompat_i, Rep.hom_comm_apply, hiDyt]
    have h2 : φ'' (c s) (D''.ρ s (deltaCochain₀ πD iD hiD y t)) = φ (ct s) (D.ρ s (D.ρ t yt - yt)) := by
      rw [← hπct s, ← hcompat_π, Rep.hom_comm_apply, hδ0]
    rw [h1, h2]
    simp only [map_add, map_sub, LinearMap.add_apply, LinearMap.sub_apply, map_mul, Module.End.mul_apply]
    rw [hφ]
    abel


-- created on 2026-10-24
