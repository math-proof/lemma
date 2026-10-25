import Mathlib
import sympy.Basic
import Def.v1.Atlas.Buildings.code.Building.InfinityMaps.Part7
open AffineBuilding


/--
[BuildingIsometry.pushforwardRay_origin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
@[path]
private lemma main
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : GeodesicRay b md} :
-- imply
  (φ.pushforwardRay ρ).origin = φ.toFun ρ.origin := by
-- proof
  rfl



/--
[BuildingIsometry.inducedMapInfinityCont_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma BuildingIsometry.inducedMapInfinityCont_mk
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : ContinuousGeodesicRay b md} :
-- imply
  φ.inducedMapInfinityCont (Quot.mk _ ρ) = Quot.mk (ContinuousGeodesicRay.Parallel b md) (φ.pushforwardContinuousRay ρ) := by
-- proof
  rfl



/--
[BuildingIsometry.pushforwardContinuousRay_origin](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma BuildingIsometry.pushforwardContinuousRay_origin
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : ContinuousGeodesicRay b md} :
-- imply
  (φ.pushforwardContinuousRay ρ).origin = φ.toFun ρ.origin := by
-- proof
  rfl



/--
[BuildingIsometry.pushforwardContinuousRay_pointAtInfinity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma BuildingIsometry.pushforwardContinuousRay_pointAtInfinity
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : ContinuousGeodesicRay b md} :
-- imply
  (φ.pushforwardContinuousRay ρ).pointAtInfinity = φ.inducedMapInfinityCont ρ.pointAtInfinity := by
-- proof
  simp only [ContinuousGeodesicRay.pointAtInfinity, BuildingIsometry.inducedMapInfinityCont_mk]



/--
[isometry_ray_formula_cont](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma isometry_ray_formula_cont
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : ContinuousGeodesicRay b md} :
-- imply
  (φ.pushforwardContinuousRay ρ).origin = φ.toFun ρ.origin ∧ (φ.pushforwardContinuousRay ρ).pointAtInfinity = φ.inducedMapInfinityCont ρ.pointAtInfinity :=
-- proof
  ⟨φ.pushforwardContinuousRay_origin ρ, φ.pushforwardContinuousRay_pointAtInfinity ρ⟩



/--
[BuildingIsometry.pushforwardRay_pointAtInfinity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma BuildingIsometry.pushforwardRay_pointAtInfinity
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : GeodesicRay b md} :
-- imply
  (φ.pushforwardRay ρ).pointAtInfinity = φ.inducedMapInfinity ρ.pointAtInfinity := by
-- proof
  simp only [GeodesicRay.pointAtInfinity, BuildingIsometry.inducedMapInfinity_mk]



/--
[inducedSimplexMapOfAuto_points](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma inducedSimplexMapOfAuto_points
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {f : V → V}
  {σ : SimplexAtInfinity b md}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  (inducedSimplexMapOfAuto f hf σ).points = (isometryOfAutomorphism md f hf).inducedMapInfinity '' σ.points :=
-- proof
  (inducedSimplexMap_exists f hf σ).choose_spec



/--
[induced_automorphism_at_infinity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma induced_automorphism_at_infinity
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {f : V → V}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  ∃ (f_inf : PointAtInfinity b md → PointAtInfinity b md), (∀ σ : SimplexAtInfinity b md, ∃ τ : SimplexAtInfinity b md, τ.points = f_inf '' σ.points) ∧ (∀ σ τ : SimplexAtInfinity b md, SimplexAtInfinity.IsFace b md σ τ → ∃ σ' τ' : SimplexAtInfinity b md, σ'.points = f_inf '' σ.points ∧ τ'.points = f_inf '' τ.points ∧ SimplexAtInfinity.IsFace b md σ' τ') ∧ (∀ ρ : GeodesicRay b md, f_inf (Quot.mk _ ρ) = Quot.mk (GeodesicRay.Parallel b md) ((isometryOfAutomorphism md f hf).pushforwardRay ρ)) := by
-- proof
  refine ⟨(isometryOfAutomorphism md f hf).inducedMapInfinity, ?_, ?_, ?_⟩
  ·
    exact fun σ => inducedSimplexMap_exists f hf σ
  ·
    intro σ τ hface
    obtain ⟨σ', hσ'⟩ := inducedSimplexMap_exists f hf σ
    obtain ⟨τ', hτ'⟩ := inducedSimplexMap_exists f hf τ
    exact ⟨σ', τ', hσ', hτ', by show σ'.points ⊆ τ'.points; rw [hσ', hτ']; exact Set.image_mono hface⟩
  ·
    exact fun ρ => (isometryOfAutomorphism md f hf).inducedMapInfinity_mk ρ



/--
[inducedSimplexMap_preserves_apartments](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma inducedSimplexMap_preserves_apartments
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {f : V → V}
  {Ainf : ApartmentAtInfinity b md}
-- given
  (hf : IsSimplicialAutomorphism b f)
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md) :
-- imply
  ∃ Ainf' ∈ allApartmentsAtInfinity b si md, ∀ σ ∈ Ainf.simplices, inducedSimplexMapOfAuto f hf σ ∈ Ainf'.simplices := by
-- proof
  simp only [allApartmentsAtInfinity, Set.mem_setOf_eq] at hAinf
  obtain ⟨A, hA, hAinf_eq⟩ := hAinf
  obtain ⟨A', hA', hA'_faces⟩ := hf.maps_apartments A hA
  refine ⟨apartmentBoundary b si md A' hA', ?_, ?_⟩
  · simp only [allApartmentsAtInfinity, Set.mem_setOf_eq]
    exact ⟨A', hA', rfl⟩
  · intro σ hσ
    subst hAinf_eq
    simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
    obtain ⟨S, hS_apt, hS_pts⟩ := hσ
    obtain ⟨S', hS'_verts, hS'_apt⟩ := automorphism_maps_sectors_apartment f hf S A' hA'
      (by intro s hs; exact hA'_faces s (by rwa [hS_apt] at hs))
    refine ⟨S', hS'_apt, ?_⟩
    rw [inducedSimplexMapOfAuto_points]
    intro p hp
    obtain ⟨q, hq_mem, hq_eq⟩ := hp
    have hq_in_S : q ∈ S.pointsAtInfinity md := hS_pts hq_mem
    simp only [Sector.pointsAtInfinity, Set.mem_setOf_eq] at hq_in_S ⊢
    obtain ⟨ρ, hρ_in_S, hq_is_ρ⟩ := hq_in_S
    subst hq_is_ρ
    rw [BuildingIsometry.inducedMapInfinity_mk] at hq_eq
    refine ⟨(isometryOfAutomorphism md f hf).pushforwardRay ρ, ?_, hq_eq.symm⟩
    intro n
    simp only [BuildingIsometry.pushforwardRay, isometryOfAutomorphism, Function.comp]
    rw [hS'_verts]
    exact ⟨ρ.toFun n, hρ_in_S n, rfl⟩



/--
[stabilizer_maps_sectors_to_same_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma stabilizer_maps_sectors_to_same_apartment
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {f : V → V}
  {A : SimplicialComplex V}
  {S : Sector b}
-- given
  (hf : IsSimplicialAutomorphism b f)
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_stab : ∀ s ∈ A.faces, s.image f ∈ A.faces)
  (hS : S.apartment = A) :
-- imply
  ∃ (S' : Sector b), S'.vertices = f '' S.vertices ∧ S'.apartment = A := by
-- proof
  have h_maps : ∀ s ∈ S.apartment.faces, s.image f ∈ A.faces := by
    intro s hs; exact h_stab s (by rw [hS] at hs; exact hs)
  exact automorphism_maps_sectors_apartment f hf S A hA h_maps



/--
[stabilizes_implies_stabilizes_infinity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma stabilizes_implies_stabilizes_infinity
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {f : V → V}
  {A : SimplicialComplex V}
  {Ainf : ApartmentAtInfinity b md}
-- given
  (hf : IsSimplicialAutomorphism b f)
  (hA : A ∈ b.apartmentSystem.apartments)
  (h_stab : ∀ s ∈ A.faces, s.image f ∈ A.faces)
  (hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
  (hAinf_from_A : Ainf.apartment = A) :
-- imply
  ∀ σ ∈ Ainf.simplices, inducedSimplexMapOfAuto f hf σ ∈ Ainf.simplices := by
-- proof
  intro σ hσ
  subst hAinf_from_A
  simp only [allApartmentsAtInfinity, Set.mem_setOf_eq] at hAinf
  obtain ⟨A₀, hA₀, hAinf_eq⟩ := hAinf
  subst hAinf_eq
  simp only [apartmentBoundary, Set.mem_setOf_eq] at hσ ⊢
  obtain ⟨S, hS_apt, hS_pts⟩ := hσ
  obtain ⟨S', hS'_verts, hS'_apt⟩ := stabilizer_maps_sectors_to_same_apartment f hf A₀ hA₀ h_stab S hS_apt
  refine ⟨S', hS'_apt, ?_⟩
  rw [inducedSimplexMapOfAuto_points]
  intro p hp
  obtain ⟨q, hq_mem, hq_eq⟩ := hp
  have hq_in_S : q ∈ S.pointsAtInfinity md := hS_pts hq_mem
  simp only [Sector.pointsAtInfinity, Set.mem_setOf_eq] at hq_in_S ⊢
  obtain ⟨ρ, hρ_in_S, hq_is_ρ⟩ := hq_in_S
  subst hq_is_ρ
  rw [BuildingIsometry.inducedMapInfinity_mk] at hq_eq
  refine ⟨(isometryOfAutomorphism md f hf).pushforwardRay ρ, ?_, hq_eq.symm⟩
  intro n
  simp only [BuildingIsometry.pushforwardRay, isometryOfAutomorphism, Function.comp]
  rw [hS'_verts]
  exact ⟨ρ.toFun n, hρ_in_S n, rfl⟩



/--
[stabilizer_infinity_implies_stabilizer](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma stabilizer_infinity_implies_stabilizer
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {si : SectorInfrastructure b}
  {md : ApartmentMetricData b}
  {f : V → V}
  {A : SimplicialComplex V}
  {Ainf : ApartmentAtInfinity b md}
-- given
  (hf : IsSimplicialAutomorphism b f)
  (hA : A ∈ b.apartmentSystem.apartments)
  (_hAinf : Ainf ∈ allApartmentsAtInfinity b si md)
  (_hAinf_from_A : Ainf.apartment = A)
  (_h_stab_inf : ∀ σ ∈ Ainf.simplices, inducedSimplexMapOfAuto f hf σ ∈ Ainf.simplices) :
-- imply
  ∀ s ∈ A.faces, s.image f ∈ A.faces := by
-- proof
  obtain ⟨A', hA', hA'_faces⟩ := hf.maps_apartments A hA
  suffices h_incl : A'.faces ⊆ A.faces from fun s hs => h_incl (hA'_faces s hs)
  obtain ⟨s₀, hs₀⟩ := b.apartmentSystem.apt_nonempty A hA
  obtain ⟨D, hD_face, hD_max, _⟩ :=
    si.apt_face_extends_to_chamber A hA s₀ hs₀
  have hD_bmax : b.toChamberComplex.toSimplicialComplex.IsMaximal D :=
    b.apartmentSystem.maximal_in_apt_is_maximal A hA D hD_max
  have hfD_A' : D.image f ∈ A'.faces := hA'_faces D hD_face
  obtain ⟨g, hg, hgf, hfg⟩ := inverse_is_automorphism f hf
  have hfD_bmax : b.toChamberComplex.toSimplicialComplex.IsMaximal (D.image f) := by
    refine ⟨hf.maps_faces D hD_bmax.1, ?_⟩
    intro T hT hDf_sub
    have hgfD : (D.image f).image g = D := by
      ext v; simp only [Finset.mem_image]
      constructor
      · rintro ⟨w, ⟨u, hu, rfl⟩, rfl⟩; rwa [hgf]
      · intro hv; exact ⟨f v, ⟨v, hv, rfl⟩, hgf v⟩
    have hTg_face : T.image g ∈ b.toChamberComplex.toSimplicialComplex.faces :=
      hg.maps_faces T hT
    have hD_sub_Tg : D ⊆ T.image g := hgfD ▸ Finset.image_subset_image hDf_sub
    have hD_eq_Tg : D = T.image g := hD_bmax.2 (T.image g) hTg_face hD_sub_Tg
    ext v; constructor
    · intro hv
      rw [Finset.mem_image] at hv
      obtain ⟨u, hu, rfl⟩ := hv
      rw [hD_eq_Tg] at hu
      rw [Finset.mem_image] at hu
      obtain ⟨w, hw, rfl⟩ := hu
      rwa [hfg w]
    · intro hv
      rw [Finset.mem_image]
      have hgv_in_D : g v ∈ D := hD_eq_Tg ▸ Finset.mem_image_of_mem g hv
      exact ⟨g v, hgv_in_D, hfg v⟩
  obtain ⟨B, hB, hD_B, hfD_B⟩ :=
    b.apartmentSystem.contains_pair D (D.image f) hD_bmax hfD_bmax
  have hB_sub_A : B.faces ⊆ A.faces :=
    apt_faces_subset b A B hA hB D hD_face hD_B hD_bmax
  have hfD_A : D.image f ∈ A.faces := hB_sub_A hfD_B
  exact apt_faces_subset b A A' hA hA' (D.image f) hfD_A hfD_A' hfD_bmax


/--
[isometry_preserves_parallelism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma isometry_preserves_parallelism_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ₁ ρ₂ : GeodesicRay b md}
-- given
  (h : GeodesicRay.Parallel b md ρ₁ ρ₂) :
-- imply
  GeodesicRay.Parallel b md (φ.pushforwardRay ρ₁) (φ.pushforwardRay ρ₂) := by
-- proof
  apply AffineBuilding.isometry_preserves_parallelism φ ρ₁ ρ₂ h

/--
[isometry_preserves_parallelism_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma isometry_preserves_parallelism_continuous_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ₁ ρ₂ : ContinuousGeodesicRay b md}
-- given
  (h : ContinuousGeodesicRay.Parallel b md ρ₁ ρ₂) :
-- imply
  ContinuousGeodesicRay.Parallel b md (φ.pushforwardContinuousRay ρ₁) (φ.pushforwardContinuousRay ρ₂) := by
-- proof
  apply AffineBuilding.isometry_preserves_parallelism_continuous φ ρ₁ ρ₂ h

/--
[BuildingIsometry.inducedMapInfinity_mk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma inducedMapInfinity_mk_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {φ : BuildingIsometry b md}
  {ρ : GeodesicRay b md} :
-- imply
  φ.inducedMapInfinity (Quot.mk _ ρ) = Quot.mk (GeodesicRay.Parallel b md) (φ.pushforwardRay ρ) := by
-- proof
  apply AffineBuilding.BuildingIsometry.inducedMapInfinity_mk φ ρ

/--
[automorphism_maps_sectors_apartment](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma automorphism_maps_sectors_apartment_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {f : V → V}
  {S : Sector b}
  {A' : SimplicialComplex V}
-- given
  (hf : IsSimplicialAutomorphism b f)
  (hA' : A' ∈ b.apartmentSystem.apartments)
  (h_maps : ∀ s ∈ S.apartment.faces, s.image f ∈ A'.faces) :
-- imply
  ∃ (S' : Sector b), S'.vertices = f '' S.vertices ∧ S'.apartment = A' := by
-- proof
  apply AffineBuilding.automorphism_maps_sectors_apartment f hf S A' hA' h_maps

/--
[automorphism_maps_sectors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma automorphism_maps_sectors_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {f : V → V}
  {S : Sector b}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  ∃ (S' : Sector b), S'.vertices = f '' S.vertices := by
-- proof
  apply AffineBuilding.automorphism_maps_sectors f hf S

/--
[injective_face_map_maximal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma injective_face_map_maximal_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C : Finset V}
-- given
  (h : V → V)
  (h_inj : Function.Injective h)
  (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
  (h_inv : V → V)
  (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
  (h_inv_left : ∀ v, h_inv (h v) = v)
  (h_right : ∀ v, h (h_inv v) = v)
  (hC : K.IsMaximal C) :
-- imply
  K.IsMaximal (C.image h) := by
-- proof
  apply AffineBuilding.injective_face_map_maximal h h_inj h_faces h_inv h_inv_faces h_inv_left h_right C hC

/--
[injective_face_map_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma injective_face_map_adjacent_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {K : SimplicialComplex V}
  {C D : Finset V}
-- given
  (h : V → V)
  (h_inj : Function.Injective h)
  (h_faces : ∀ s ∈ K.faces, s.image h ∈ K.faces)
  (h_inv : V → V)
  (h_inv_faces : ∀ s ∈ K.faces, s.image h_inv ∈ K.faces)
  (h_inv_left : ∀ v, h_inv (h v) = v)
  (h_right : ∀ v, h (h_inv v) = v)
  (hadj : K.Adjacent C D) :
-- imply
  K.Adjacent (C.image h) (D.image h) := by
-- proof
  apply AffineBuilding.injective_face_map_adjacent h h_inj h_faces h_inv h_inv_faces h_inv_left h_right C D hadj

/--
[inverse_is_automorphism](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma inverse_is_automorphism_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {f : V → V}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  ∃ (g : V → V), IsSimplicialAutomorphism b g ∧ (∀ v, g (f v) = v) ∧ (∀ v, f (g v) = v) := by
-- proof
  apply AffineBuilding.inverse_is_automorphism f hf

/--
[automorphism_is_isometry](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma automorphism_is_isometry_eq
  {V : Type}
  [DecidableEq V]
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {f : V → V}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  ∀ v w : V, buildingDist b md (f v) (f w) = buildingDist b md v w := by
-- proof
  apply AffineBuilding.automorphism_is_isometry md f hf

/--
[inducedSimplexMap_exists](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/InfinityMaps.lean)
-/
private lemma inducedSimplexMap_exists_eq
  {V : Type}
  [DecidableEq V]
  {b : Building V}
  {md : ApartmentMetricData b}
  {f : V → V}
  {σ : SimplexAtInfinity b md}
-- given
  (hf : IsSimplicialAutomorphism b f) :
-- imply
  ∃ (τ : SimplexAtInfinity b md), τ.points = (isometryOfAutomorphism md f hf).inducedMapInfinity '' σ.points := by
-- proof
  apply AffineBuilding.inducedSimplexMap_exists f hf σ


-- created on 2026-10-23
-- updated on 2026-10-24
