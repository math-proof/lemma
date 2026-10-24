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
[groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_cup_deltaCochain0_add_cup02_deltaCochain1_mem_levelCoboundaries2.lean)
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
  {c : M''}
  {y : cocycles₁ D'}
-- given
  (hπ : Function.Surjective π.hom)
  (hex : ∀ m : M, π.hom m = 0 ↔ ∃ m' : M', i.hom m' = m)
  (hiD : Function.Surjective iD.hom)
  (hexD : ∀ x : D, iD.hom x = 0 ↔ ∃ y : D'', πD.hom y = x)
  (hφ : Rep.IsEquivariantBilinear M D N φ)
  (hcompat_i : ∀ (m' : M') (x : D), φ (i.hom m') x = φ' m' (iD.hom x))
  (hcompat_π : ∀ (m : M) (y : D''), φ m (πD.hom y) = φ'' (π.hom m) y)
  (hc : ∀ s, M''.ρ s c = c)
  (hy : IsLevelConstant₁ r (⇑y)) :
-- imply
  (cupCochain φ' (deltaCochain₀ i π hπ c) (⇑y)
        + fun st => φ'' c (deltaCochain₁ πD iD hiD (⇑y) st))
      ∈ levelCoboundaries₂ r N := by
-- proof
  set mt : M := Function.surjInv hπ c with hmt
  set yt : G → D := Function.surjInv hiD ∘ (⇑y) with hyt
  have hπmt : π.hom mt = c := Function.surjInv_eq hπ c
  have hiDyt : ∀ g, iD.hom (yt g) = y g := fun g => Function.surjInv_eq hiD (y g)
  have hδ0 : ∀ s, i.hom (deltaCochain₀ i π hπ c s) = M.ρ s mt - mt := by
    intro s
    rw [deltaCochain₀_apply]
    refine apply_preimageFun i ((hex _).1 ?_)
    rw [map_sub, Rep.hom_comm_apply, hπmt, hc s, sub_self]
  have hδ1 : ∀ s t, πD.hom (deltaCochain₁ πD iD hiD (⇑y) (s, t)) = D.ρ s (yt t) - yt (s * t) + yt s := by
    intro s t
    rw [deltaCochain₁_apply]
    refine apply_preimageFun πD ((hexD _).1 ?_)
    rw [map_add, map_sub, Rep.hom_comm_apply]
    change D'.ρ s (iD.hom (yt t)) - iD.hom (yt (s * t)) + iD.hom (yt s) = 0
    rw [hiDyt, hiDyt, hiDyt, (mem_cocycles₁_iff (⇑y)).1 y.2 s t]
    abel
  refine (mem_levelCoboundaries₂_iff r N _).2 ⟨fun s => φ mt (yt s), ?_, ?_⟩
  ·
    obtain ⟨F, hF, hF'⟩ := hy
    refine ⟨F, hF, fun g s hs => ?_⟩
    show φ mt (yt (g * s)) = φ mt (yt g)
    rw [hyt, Function.comp_apply, Function.comp_apply, hF' g s hs]
  ·
    funext ⟨s, t⟩
    rw [d₁₂_hom_apply, Pi.add_apply, cupCochain_apply]
    change N.ρ s (φ mt (yt t)) - φ mt (yt (s * t)) + φ mt (yt s) =
      φ' (deltaCochain₀ i π hπ c s) (D'.ρ s (y t)) + φ'' c (deltaCochain₁ πD iD hiD (⇑y) (s, t))
    have h1 : φ' (deltaCochain₀ i π hπ c s) (D'.ρ s (y t)) = φ (M.ρ s mt - mt) (D.ρ s (yt t)) := by
      rw [← hδ0, hcompat_i, Rep.hom_comm_apply, hiDyt]
    have h2 : φ'' c (deltaCochain₁ πD iD hiD (⇑y) (s, t)) = φ mt (D.ρ s (yt t) - yt (s * t) + yt s) := by
      rw [← hδ1, hcompat_π, hπmt]
    rw [h1, h2, map_sub, LinearMap.sub_apply, hφ, map_add, map_sub]
    abel


-- created on 2026-10-24
