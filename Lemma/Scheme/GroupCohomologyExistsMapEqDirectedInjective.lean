import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u v

variable {k G : Type u} [CommRing k] [Group G]
private lemma exists_cocycle_lift
  {A B : Rep k G} (ι : A ⟶ B) (hι : Function.Injective ι.hom) (n : ℕ)
  (u : (Fin n → G) → B) (hu : ∀ g, u g ∈ Set.range ι.hom)
  (hdu : (groupCohomology.inhomogeneousCochains B).d n (n + 1) u = 0) :
  ∃ u' : (Fin n → G) → A, (groupCohomology.cochainsMap (MonoidHom.id G) ι).f n u' = u ∧
    (groupCohomology.inhomogeneousCochains A).d n (n + 1) u' = 0 := by
  choose u' hu' using hu
  have hmap : (groupCohomology.cochainsMap (MonoidHom.id G) ι).f n u' = u := by
    funext g
    rw [groupCohomology.cochainsMap_f]
    refine hu' g
  refine ⟨u', hmap, ?_⟩
  let _ : Mono ι := (Rep.mono_iff_injective ι).mpr hι
  apply (ModuleCat.mono_iff_injective ((groupCohomology.cochainsMap (MonoidHom.id G) ι).f (n + 1))).mp inferInstance
  have hcomm := (groupCohomology.cochainsMap (MonoidHom.id G) ι).comm n (n + 1)
  have h1 : ((groupCohomology.cochainsMap (MonoidHom.id G) ι).f (n + 1))
    ((groupCohomology.inhomogeneousCochains A).d n (n + 1) u') =
    (groupCohomology.inhomogeneousCochains B).d n (n + 1) ((groupCohomology.cochainsMap (MonoidHom.id G) ι).f n u') := by
    have h := congrArg (fun φ => (ModuleCat.Hom.hom φ) u') hcomm
    simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply]
    refine h.symm
  rw [map_zero, h1, hmap, hdu]
private lemma exists_map_eq
  [Finite G] {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {B : Rep k G} (A : I → Rep k G) (ι : ∀ i, A i ⟶ B) (hι : ∀ i, Function.Injective (ι i).hom)
  (hmono : ∀ i j, i ≤ j → Set.range (ι i).hom ⊆ Set.range (ι j).hom)
  (hcov : ∀ b : B, ∃ i, b ∈ Set.range (ι i).hom) (n : ℕ) (x : groupCohomology B n) (i₀ : I) :
  ∃ i, i₀ ≤ i ∧ ∃ y : groupCohomology (A i) n,
    (groupCohomology.map (MonoidHom.id G) (ι i) n).hom y = x := by
  classical
  let _ : Nonempty I := ⟨i₀⟩
  induction x using groupCohomology_induction_on
  rename_i z
  set u : (Fin n → G) → B := (groupCohomology.iCocycles B n).hom z with hu
  let _ : Fintype G := Fintype.ofFinite G
  choose iof hiof using hcov
  obtain ⟨i, hi⟩ := Finset.exists_le (insert i₀ (Finset.univ.image (fun g : Fin n → G => iof (u g))))
  have hi₀ : i₀ ≤ i := hi _ (Finset.mem_insert_self _ _)
  have hvals : ∀ g, u g ∈ Set.range (ι i).hom := fun g =>
    hmono _ _ (hi _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ g)))) (hiof (u g))
  have hdu : (groupCohomology.inhomogeneousCochains B).d n (n + 1) u = 0 := by
    rw [hu]
    change ((groupCohomology.iCocycles B n) ≫ (groupCohomology.inhomogeneousCochains B).d n (n + 1)).hom z = 0
    rw [HomologicalComplex.iCycles_d, ModuleCat.hom_zero, LinearMap.zero_apply]
  obtain ⟨u', hu', hdu'⟩ := exists_cocycle_lift (ι i) (hι i) n u hvals hdu
  refine ⟨i, hi₀, groupCohomology.π (A i) n (groupCohomology.cocyclesMk u' ?_), ?_⟩
  ·
    rw [groupCohomology.inhomogeneousCochains.d_def]
    refine hdu'
  have hπ := HomologicalComplex.homologyπ_naturality (groupCohomology.cochainsMap (MonoidHom.id G) (ι i)) n
  change ((groupCohomology.π (A i) n) ≫ groupCohomology.map (MonoidHom.id G) (ι i) n).hom _ = _
  erw [hπ]
  change (groupCohomology.π B n).hom ((groupCohomology.cocyclesMap (MonoidHom.id G) (ι i) n).hom
    (groupCohomology.cocyclesMk u' _)) = (groupCohomology.π B n).hom z
  congr 1
  apply (ModuleCat.mono_iff_injective (groupCohomology.iCocycles B n)).mp inferInstance
  change ((groupCohomology.cocyclesMap (MonoidHom.id G) (ι i) n) ≫ groupCohomology.iCocycles B n).hom _ = _
  rw [HomologicalComplex.cyclesMap_i, ModuleCat.hom_comp, LinearMap.comp_apply]
  erw [groupCohomology.iCocycles_mk]
  rw [hu']
/--
[groupCohomology_exists_map_eq_of_directed_of_injective](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_groupCohomology_exists_map_eq_of_directed_of_injective.lean)
-/
@[path]
private lemma main
  [Finite G]
  {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  {B : Rep k G} (A : I → Rep k G) (ι : ∀ i, A i ⟶ B) (hι : ∀ i, Function.Injective (ι i).hom)
  (hmono : ∀ i j, i ≤ j → Set.range (ι i).hom ⊆ Set.range (ι j).hom)
  (hcov : ∀ b : B, ∃ i, b ∈ Set.range (ι i).hom)
  (n : ℕ) (x : groupCohomology B n) (i₀ : I) :
  -- imply
  ∃ i, i₀ ≤ i ∧ ∃ y : groupCohomology (A i) n, (groupCohomology.map (MonoidHom.id G) (ι i) n).hom y = x :=
  exists_map_eq A ι hι hmono hcov n x i₀


-- created on 2026-10-20
