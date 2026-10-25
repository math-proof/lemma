import Mathlib
import sympy.Basic
import Lemma.GroupCohomology.TateCohomology
import Lemma.GroupCohomology.TateSeam
import Lemma.Int.P2MUtil

open CategoryTheory Rep

/--
[Rep_exact_tateDeltaNeg2_tateHneg1Map](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Rep_exact_tateDeltaNeg2_tateHneg1Map.lean)
-/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G] [Fintype G]
  {X : ShortComplex (Rep.{u} k G)}
-- given
  (hX : X.ShortExact) :
-- imply
  Function.Exact (Rep.tateδneg2 hX) (Rep.tateHneg1Map X.f) := by
-- proof
  have h1 : LinearMap.range (groupHomology.δ hX 1 0 rfl).hom =
      LinearMap.ker (groupHomology.map (MonoidHom.id G) X.f 0).hom :=
    (groupHomology.mapShortComplex₁_exact hX (rfl : 0 + 1 = 1)).moduleCat_range_eq_ker
  have hnat : ∀ u, (groupHomology.H0Iso X.X₂).hom ((groupHomology.map (MonoidHom.id G) X.f 0) u) =
      Rep.coinvariantsMap X.f ((groupHomology.H0Iso X.X₁).hom u) :=
    fun u => groupHomology.map_id_comp_H0Iso_hom_apply X.f u
  intro x
  rw [Subtype.ext_iff, Rep.coe_tateHneg1Map_apply]
  change Rep.coinvariantsMap X.f (x : X.X₁.ρ.Coinvariants) = 0 ↔ _
  constructor
  · intro hx
    have hu : (groupHomology.H0Iso X.X₁).inv (x : X.X₁.ρ.Coinvariants) ∈
        LinearMap.ker (groupHomology.map (MonoidHom.id G) X.f 0).hom := by
      rw [LinearMap.mem_ker]
      have h := hnat ((groupHomology.H0Iso X.X₁).inv (x : X.X₁.ρ.Coinvariants))
      rw [CategoryTheory.Iso.inv_hom_id_apply, hx] at h

      have h' := congrArg (groupHomology.H0Iso X.X₂).inv h
      rw [CategoryTheory.Iso.hom_inv_id_apply] at h'
      exact h'.trans (LinearMap.map_zero _)
    rw [← h1] at hu
    obtain ⟨z, hz⟩ := hu
    refine ⟨z, Subtype.ext ?_⟩
    rw [Rep.coe_tateδneg2_apply]
    change (groupHomology.H0Iso X.X₁).hom ((groupHomology.δ hX 1 0 rfl).hom z) = (x : X.X₁.ρ.Coinvariants)
    rw [hz]
    exact CategoryTheory.Iso.inv_hom_id_apply _ _
  · rintro ⟨z, rfl⟩
    rw [Rep.coe_tateδneg2_apply, ← hnat]
    have : (groupHomology.δ hX 1 0 rfl) z ∈ LinearMap.ker (groupHomology.map (MonoidHom.id G) X.f 0).hom := by
      rw [← h1]; exact LinearMap.mem_range_self _ _
    rw [LinearMap.mem_ker] at this
    change (groupHomology.H0Iso X.X₂).hom ((groupHomology.map (MonoidHom.id G) X.f 0).hom ((groupHomology.δ hX 1 0 rfl) z)) = 0
    rw [this]
    exact LinearMap.map_zero _


-- created on 2026-10-23
