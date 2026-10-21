import Mathlib
import sympy.Basic
open CategoryTheory AlgebraicGeometry Opposite
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


universe u

private lemma mul_self_eq_zero_of_app_eq_zero
  {X X' : (Scheme : Type (u + 1))} (i : X ⟶ X')
  (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : X'.presheaf.obj (op V), (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
  {U : X'.Opens} (ε : X'.presheaf.obj (op U)) (hε : (i.app U).hom ε = 0) :
  -- imply
  ε * ε = 0 := by
  -- proof
  apply X'.IsSheaf.section_ext
  intro y hy
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hy U.2
  refine ⟨V, hVU, hyV, ?_⟩
  have hres : (i.app V).hom ((X'.presheaf.map (homOfLE hVU).op) ε) = 0 := by
    change (X'.presheaf.map (homOfLE hVU).op ≫ i.app V) ε = 0
    rw [i.naturality, CommRingCat.comp_apply]
    change (X.presheaf.map _) ((i.app U).hom ε) = 0
    rw [hε, map_zero]
  rw [map_mul, map_zero]
  apply hsq V hV _ _ hres hres

/--
[AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicGeometry_isAffineOpen_of_isAffineOpen_preimage_of_app_surjective_of_mul_eq_zero.lean)
-/
@[path]
private lemma main
  {X X' : (Scheme : Type (u + 1))} (i : X ⟶ X') [Surjective i]
  (hsq : ∀ (V : X'.Opens), IsAffineOpen V → ∀ a b : X'.presheaf.obj (op V), (i.app V).hom a = 0 → (i.app V).hom b = 0 → a * b = 0)
  (U : X'.Opens) (hU : IsAffineOpen ((TopologicalSpace.Opens.map i.base).obj U)) (hsurj : Function.Surjective (i.app U).hom) :
  -- imply
  IsAffineOpen U := by
  -- proof
  let t : Set (X'.presheaf.obj (op U)) := {g | IsAffineOpen (X'.basicOpen g)}
  refine isAffineOpen_of_isAffineOpen_basicOpen U t ?_ (fun g hg => hg)
  have hcover : Ideal.span ((i.app U).hom '' t) = ⊤ := by
    rw [← hU.self_le_iSup_basicOpen_iff]
    intro x hx
    have hix : i x ∈ U := hx
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open hix U.2
    obtain ⟨f, hfV, hxf⟩ := hU.exists_basicOpen_le (V := (TopologicalSpace.Opens.map i.base).obj V) ⟨x, hxV⟩ hx
    obtain ⟨g, rfl⟩ := hsurj f
    have hgV : X'.basicOpen g ≤ V := by
      intro y hy
      obtain ⟨x', rfl⟩ := i.surjective y
      have hx' : x' ∈ (TopologicalSpace.Opens.map i.base).obj (X'.basicOpen g) := hy
      rw [Scheme.preimage_basicOpen] at hx'
      apply hfV hx'
    have hgt : g ∈ t := by
      show IsAffineOpen (X'.basicOpen g)
      rw [← inf_eq_right.mpr hgV, ← X'.basicOpen_res g (homOfLE hVU).op]
      apply hV.basicOpen _
    refine TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨(i.app U).hom g, g, hgt, rfl⟩, hxf⟩
  have h1 : (1 : X.presheaf.obj (op ((TopologicalSpace.Opens.map i.base).obj U))) ∈ Ideal.map (i.app U).hom (Ideal.span t) := by
    rw [Ideal.map_span, hcover]
    trivial
  obtain ⟨j, hj, hj1⟩ := (Ideal.mem_map_iff_of_surjective (i.app U).hom hsurj).mp h1
  have hε : (i.app U).hom (j - 1) = 0 := by
    rw [map_sub, hj1, map_one, sub_self]
  have hnil : IsNilpotent (j - 1) := by
    refine ⟨2, ?_⟩
    rw [pow_two]
    apply mul_self_eq_zero_of_app_eq_zero i hsq (j - 1) hε
  have hunit : IsUnit j := by
    have h := hnil.isUnit_one_add
    have e : (1 : X'.presheaf.obj (op U)) + (j - 1) = j := by
      ring
    rwa [e] at h
  refine Ideal.eq_top_of_isUnit_mem _ hj hunit


-- created on 2026-10-20
