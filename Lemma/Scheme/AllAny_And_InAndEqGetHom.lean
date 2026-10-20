import Mathlib
import sympy.Basic
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

private lemma mem_iInf_iff
  {X : (Scheme : Type (u + 1))} {ι : Type v} [Finite ι] (U : ι → X.Opens) (x : X) :
  x ∈ (⨅ i, U i) ↔ ∀ i, x ∈ U i := by
  constructor
  ·
    intro h i
    apply (iInf_le U i) h
  ·
    intro h
    let _ := Fintype.ofFinite ι
    rw [← Finset.inf_univ_eq_iInf]
    simp only [← SetLike.mem_coe, TopologicalSpace.Opens.coe_finset_inf, Finset.inf_set_eq_iInter]
    simpa using h

/--
[AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_Scheme_forall_exists_isAffineOpen_invariant_of_isSeparated_of_finset.lean)
-/
@[path]
private lemma main
  {B : Type u} [CommRing B] {X : (Scheme : Type (u + 1))} (πX : X ⟶ Spec (CommRingCat.of B)) (hsep : IsSeparated πX)
  (hAF : ∀ F : Finset X, ∃ U : X.Opens, IsAffineOpen U ∧ ∀ x ∈ F, x ∈ U)
  {G : Type v} [Group G] [Finite G] (ρ : G →* Aut X) :
  -- imply
  ∀ x : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ ∀ g : G, ((TopologicalSpace.Opens.map ((ρ g).hom.base)).obj U) = U := by
  -- proof
  classical
  intro x
  let _ : Fintype G := Fintype.ofFinite G
  let _ : X.IsSeparated := by
    have : IsSeparated (πX ≫ Limits.terminal.from _) := inferInstance
    rw [Limits.terminal.comp_from] at this
    refine ⟨this⟩
  obtain ⟨U₀, hU₀, hmem⟩ := hAF (Finset.univ.image fun g : G => (ρ g).hom.base x)
  refine ⟨⨅ g : G, ((TopologicalSpace.Opens.map ((ρ g).hom.base)).obj U₀), ?_, ?_, ?_⟩
  · apply IsAffineOpen.iInf (fun g => hU₀.preimage_of_isIso (ρ g).hom)
  ·
    rw [mem_iInf_iff]
    intro g
    apply hmem _ (Finset.mem_image.2 ⟨g, Finset.mem_univ _, rfl⟩)
  ·
    intro h
    ext y
    constructor
    ·
      intro hy
      change (ρ h).hom.base y ∈ (⨅ g : G, ((TopologicalSpace.Opens.map ((ρ g).hom.base)).obj U₀)) at hy
      rw [mem_iInf_iff] at hy
      rw [SetLike.mem_coe, mem_iInf_iff]
      intro g
      have := hy (g * h⁻¹)
      change (ρ (g * h⁻¹)).hom.base ((ρ h).hom.base y) ∈ U₀ at this
      have hcomp : (ρ h).hom ≫ (ρ (g * h⁻¹)).hom = (ρ g).hom := by
        rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul, mul_assoc, inv_mul_cancel, mul_one]
      rw [← Scheme.Hom.comp_apply, hcomp] at this
      apply this
    ·
      intro hy
      rw [SetLike.mem_coe, mem_iInf_iff] at hy
      change (ρ h).hom.base y ∈ (⨅ g : G, ((TopologicalSpace.Opens.map ((ρ g).hom.base)).obj U₀))
      rw [mem_iInf_iff]
      intro g
      change ((ρ h).hom ≫ (ρ g).hom).base y ∈ U₀
      have hcomp : (ρ h).hom ≫ (ρ g).hom = (ρ (g * h)).hom := by
        rw [← Iso.trans_hom, ← Aut.Aut_mul_def, ← map_mul]
      rw [hcomp]
      apply hy (g * h)


-- created on 2026-10-20
