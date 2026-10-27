import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.AffineMetricGR.Part2
open Classical ChamberComplex AffineBuilding
open ChamberComplex


/--
[buildingDist_wellDefined_via_iso_fix](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/AffineMetricGR.lean)
-/
@[path]
private lemma main
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {v w : V}
-- given
  (A₁ A₂ : { A : SimplicialComplex V // A ∈ b.apartmentSystem.apartments })
  (hv₁ : ∃ s ∈ A₁.val.faces, v ∈ s)
  (hw₁ : ∃ s ∈ A₁.val.faces, w ∈ s)
  (hv₂ : ∃ s ∈ A₂.val.faces, v ∈ s)
  (hw₂ : ∃ s ∈ A₂.val.faces, w ∈ s) :
-- imply
  md.dist_fn A₁ v w = md.dist_fn A₂ v w := by
-- proof
  obtain ⟨sv₁, hsv₁, hv_sv₁⟩ := hv₁
  have hv_sing₁ : {v} ∈ A₁.val.faces :=
    A₁.val.down_closed hsv₁ (Finset.singleton_subset_iff.mpr hv_sv₁) (Finset.singleton_nonempty v)
  obtain ⟨sw₁, hsw₁, hw_sw₁⟩ := hw₁
  have hw_sing₁ : {w} ∈ A₁.val.faces :=
    A₁.val.down_closed hsw₁ (Finset.singleton_subset_iff.mpr hw_sw₁) (Finset.singleton_nonempty w)
  obtain ⟨sv₂, hsv₂, hv_sv₂⟩ := hv₂
  have hv_sing₂ : {v} ∈ A₂.val.faces :=
    A₂.val.down_closed hsv₂ (Finset.singleton_subset_iff.mpr hv_sv₂) (Finset.singleton_nonempty v)
  obtain ⟨sw₂, hsw₂, hw_sw₂⟩ := hw₂
  have hw_sing₂ : {w} ∈ A₂.val.faces :=
    A₂.val.down_closed hsw₂ (Finset.singleton_subset_iff.mpr hw_sw₂) (Finset.singleton_nonempty w)
  exact buildingDist_well_defined_clean b md v w A₁ A₂ hv_sing₁ hw_sing₁ hv_sing₂ hw_sing₂



-- created on 2026-10-23
-- updated on 2026-10-26
