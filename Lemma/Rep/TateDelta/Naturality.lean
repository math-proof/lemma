import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.GroupCohomology.TateSeam
import Lemma.GroupCohomology.TateShiftMaps
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_tateDelta_naturality](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_tateDelta_naturality.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {X Y : ShortComplex (Rep.{u} k G)}
  {τ : X ⟶ Y}
  {n : ℤ}
-- given
  (hX : X.ShortExact)
  (hY : Y.ShortExact) :
-- imply
  Rep.tateδ hX n ≫ Rep.tateMap τ.τ₁ (n + 1) = Rep.tateMap τ.τ₃ n ≫ Rep.tateδ hY n := by
-- proof
  match n with
  | Int.ofNat (m + 1) =>
    exact HomologicalComplex.HomologySequence.δ_naturality
      ((groupCohomology.cochainsFunctor k G).mapShortComplex.map τ)
      (groupCohomology.map_cochainsFunctor_shortExact hX) (groupCohomology.map_cochainsFunctor_shortExact hY)
      (m + 1) (m + 2) rfl
  | Int.ofNat 0 =>

    show ModuleCat.ofHom (Rep.tateδ₀ hX) ≫ groupCohomology.map (MonoidHom.id G) τ.τ₁ 1
      = ModuleCat.ofHom (Rep.tateH0Map τ.τ₃) ≫ ModuleCat.ofHom (Rep.tateδ₀ hY)
    have hδ := HomologicalComplex.HomologySequence.δ_naturality
      ((groupCohomology.cochainsFunctor k G).mapShortComplex.map τ)
      (groupCohomology.map_cochainsFunctor_shortExact hX) (groupCohomology.map_cochainsFunctor_shortExact hY) 0 1 rfl
    have hH0 := groupCohomology.map_id_comp_H0Iso_hom τ.τ₃
    apply ModuleCat.hom_ext
    refine Submodule.linearMap_qext _ (LinearMap.ext fun z => ?_)
    change (groupCohomology.map (MonoidHom.id G) τ.τ₁ 1).hom (Rep.tateδ₀ hX (Submodule.Quotient.mk z))
      = Rep.tateδ₀ hY (Rep.tateH0Map τ.τ₃ (Submodule.Quotient.mk z))
    rw [Rep.tateH0Map_mk, Rep.tateδ₀_mk, Rep.tateδ₀_mk]
    have h1 := congrArg (fun ψ => ψ.hom ((groupCohomology.H0Iso X.X₃).inv z)) hδ
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at h1
    change (groupCohomology.map (MonoidHom.id G) τ.τ₁ 1).hom
        ((groupCohomology.δ hX 0 1 rfl).hom ((groupCohomology.H0Iso X.X₃).inv z))
      = (groupCohomology.δ hY 0 1 rfl).hom ((groupCohomology.map (MonoidHom.id G) τ.τ₃ 0).hom ((groupCohomology.H0Iso X.X₃).inv z)) at h1
    rw [h1]
    congr 1

    have e1 : (groupCohomology.H0Iso X.X₃).hom.hom ((groupCohomology.H0Iso X.X₃).inv.hom z) = z :=
      congrArg (fun ψ => ψ.hom z) (groupCohomology.H0Iso X.X₃).inv_hom_id
    have e2 : ∀ w, (groupCohomology.H0Iso Y.X₃).inv.hom ((groupCohomology.H0Iso Y.X₃).hom.hom w) = w := fun w =>
      congrArg (fun ψ => ψ.hom w) (groupCohomology.H0Iso Y.X₃).hom_inv_id
    have h2 := congrArg (fun ψ => (groupCohomology.H0Iso Y.X₃).inv.hom (ψ.hom ((groupCohomology.H0Iso X.X₃).inv.hom z))) hH0
    change (groupCohomology.H0Iso Y.X₃).inv.hom ((groupCohomology.H0Iso Y.X₃).hom.hom
        ((groupCohomology.map (MonoidHom.id G) τ.τ₃ 0).hom ((groupCohomology.H0Iso X.X₃).inv.hom z)))
      = (groupCohomology.H0Iso Y.X₃).inv.hom (((Rep.invariantsFunctor k G).map τ.τ₃).hom
        ((groupCohomology.H0Iso X.X₃).hom.hom ((groupCohomology.H0Iso X.X₃).inv.hom z))) at h2
    rw [e2, e1] at h2
    exact h2
  | Int.negSucc 0 =>

    show ModuleCat.ofHom (Rep.tateδneg1 hX) ≫ ModuleCat.ofHom (Rep.tateH0Map τ.τ₁)
      = ModuleCat.ofHom (Rep.tateHneg1Map τ.τ₃) ≫ ModuleCat.ofHom (Rep.tateδneg1 hY)
    rw [← ModuleCat.ofHom_comp, ← ModuleCat.ofHom_comp]
    congr 1
    apply LinearMap.ext
    intro x
    obtain ⟨⟨b, hb⟩, rfl⟩ := Rep.seamθ_surjective hX x

    let a : X.X₁.ρ.invariants := ⟨Rep.seamψ hX ⟨b, hb⟩, Rep.seamψ_mem_invariants hX ⟨b, hb⟩⟩
    have hab : X.f.hom a = X.X₂.ρ.norm b := Rep.f_seamψ hX ⟨b, hb⟩

    have hc : Y.g.hom (τ.τ₂.hom b) = τ.τ₃.hom (X.g.hom b) := by
      rw [← Rep.comp_apply, τ.comm₂₃, Rep.comp_apply]
    have hb' : Y.X₃.ρ.norm (Y.g.hom (τ.τ₂.hom b)) = 0 := by
      rw [hc, ← Rep.hom_norm_apply, show X.X₃.ρ.norm (X.g.hom b) = 0 from hb, map_zero]
    have hab' : Y.f.hom (Rep.invariantsMap τ.τ₁ a) = Y.X₂.ρ.norm (τ.τ₂.hom b) := by
      rw [Rep.coe_invariantsMap_apply, ← Rep.comp_apply, τ.comm₁₂, Rep.comp_apply, hab, Rep.hom_norm_apply]
    have hθ : Rep.tateHneg1Map τ.τ₃ (Rep.seamθ X ⟨b, hb⟩) = Rep.seamθ Y ⟨τ.τ₂.hom b, hb'⟩ := by
      apply Subtype.ext
      rw [Rep.coe_tateHneg1Map_apply, Rep.coe_seamθ_apply, Rep.coe_seamθ_apply, Rep.coinvariantsMap_mk, hc]
    rw [LinearMap.comp_apply, LinearMap.comp_apply, Rep.tateδneg1_mk hX b hb a hab, Rep.tateH0Map_mk, hθ,
      Rep.tateδneg1_mk hY (τ.τ₂.hom b) hb' (Rep.invariantsMap τ.τ₁ a) hab']
  | Int.negSucc 1 =>

    show ModuleCat.ofHom (Rep.tateδneg2 hX) ≫ ModuleCat.ofHom (Rep.tateHneg1Map τ.τ₁)
      = groupHomology.map (MonoidHom.id G) τ.τ₃ 1 ≫ ModuleCat.ofHom (Rep.tateδneg2 hY)
    have hδ := HomologicalComplex.HomologySequence.δ_naturality
      ((groupHomology.chainsFunctor k G).mapShortComplex.map τ)
      (groupHomology.map_chainsFunctor_shortExact hX) (groupHomology.map_chainsFunctor_shortExact hY) 1 0 rfl
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    apply Subtype.ext
    change Rep.coinvariantsMap τ.τ₁ ((groupHomology.H0Iso X.X₁).hom (groupHomology.δ hX 1 0 rfl z))
      = (groupHomology.H0Iso Y.X₁).hom (groupHomology.δ hY 1 0 rfl (groupHomology.map (MonoidHom.id G) τ.τ₃ 1 z))
    have h1 := congrArg (fun ψ => ψ.hom z) hδ
    change (groupHomology.map (MonoidHom.id G) τ.τ₁ 0).hom (groupHomology.δ hX 1 0 rfl z)
      = groupHomology.δ hY 1 0 rfl (groupHomology.map (MonoidHom.id G) τ.τ₃ 1 z) at h1
    rw [← h1]
    exact (groupHomology.map_id_comp_H0Iso_hom_apply τ.τ₁ _).symm
  | Int.negSucc (m + 2) =>
    exact HomologicalComplex.HomologySequence.δ_naturality
      ((groupHomology.chainsFunctor k G).mapShortComplex.map τ)
      (groupHomology.map_chainsFunctor_shortExact hX) (groupHomology.map_chainsFunctor_shortExact hY)
      (m + 2) (m + 1) rfl


-- created on 2026-10-23
