import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.Buildings.code.Building.StrongIsometryExt


/--
[Building.WValuedDist.delta_retraction_preserves](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/StrongIsometryExt.lean)
-/
@[path]
lemma Building.WValuedDist.delta_retraction_preserves
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C) :
-- imply
  ∃ (ρbar : Finset V → Finset V), (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → ρbar D ∈ A.faces ∧ A.IsMaximal (ρbar D)) ∧ (∀ D, D ∈ A.faces → A.IsMaximal D → ρbar D = D) ∧ (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta C (ρbar D) = δW.delta C D) ∧ (∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta (ρbar D) C = δW.delta D C) ∧ (∀ D₁ D₂, b.toChamberComplex.toSimplicialComplex.Adjacent D₁ D₂ → ρbar D₁ = ρbar D₂ ∨ A.Adjacent (ρbar D₁) (ρbar D₂)) := by
-- proof
  obtain ⟨B_idx, M, cc, hcc_eq, φ, hφ_inj, hφ_surj, hφ_adj, _⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA
  obtain ⟨iso, hiso⟩ := δW.delta_apt_compat A hA B_idx M φ hφ_inj hφ_surj
  have hC_bldg : b.toChamberComplex.toSimplicialComplex.IsMaximal C :=
    b.apartmentSystem.maximal_in_apt_is_maximal A hA C hC
  have exists_preimage : ∀ D, ∃ E, A.IsMaximal E ∧ φ E = φ C * iso (δW.delta C D) := by
    intro D; exact hφ_surj (φ C * iso (δW.delta C D))
  let ρbar : Finset V → Finset V := fun D => (exists_preimage D).choose
  have hρbar_max : ∀ D, A.IsMaximal (ρbar D) :=
    fun D => (exists_preimage D).choose_spec.1
  have hρbar_φ : ∀ D, φ (ρbar D) = φ C * iso (δW.delta C D) :=
    fun D => (exists_preimage D).choose_spec.2
  have hρbar_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D →
    δW.delta C (ρbar D) = δW.delta C D := by
    intro D _
    have hρD := hρbar_max D
    have h1 := hiso C (ρbar D) hC.1 hC hρD.1 hρD
    rw [hρbar_φ D] at h1
    have h3 : iso (δW.delta C (ρbar D)) = iso (δW.delta C D) := by
      rw [h1, inv_mul_cancel_left]
    exact iso.injective h3
  refine ⟨ρbar, ?_, ?_, ?_, ?_, ?_⟩
  · intro D _; exact ⟨(hρbar_max D).1, hρbar_max D⟩
  · intro D hD_mem hD_max
    have hD_bldg := b.apartmentSystem.maximal_in_apt_is_maximal A hA D hD_max
    have hρD := hρbar_max D
    have h_eq := hρbar_delta D hD_bldg
    have h1 := hiso C (ρbar D) hC.1 hC hρD.1 hρD
    have h2 := hiso C D hC.1 hC hD_mem hD_max
    rw [h_eq] at h1
    have h3 : φ (ρbar D) = φ D := mul_left_cancel (h1.symm.trans h2)
    exact hφ_inj (ρbar D) hρD D hD_max h3
  · exact hρbar_delta
  · intro D hD
    have hρD := hρbar_max D
    have h_rC := hiso (ρbar D) C hρD.1 hρD hC.1 hC
    have h_Cr := hiso C (ρbar D) hC.1 hC hρD.1 hρD
    have h_anti_rho : iso (δW.delta (ρbar D) C) = (iso (δW.delta C (ρbar D)))⁻¹ := by
      rw [h_rC, h_Cr, mul_inv_rev, inv_inv]
    obtain ⟨A', hA', hC_A', hD_A'⟩ := b.apartmentSystem.contains_pair C D hC_bldg hD
    have hC_max_A' := b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A' hA' C hC_A' hC_bldg
    have hD_max_A' := b.apartmentSystem.building_maximal_in_apt_is_apt_maximal A' hA' D hD_A' hD
    obtain ⟨B_idx', M', cc', hcc_eq', φ', hφ'_inj, hφ'_surj, _⟩ :=
      b.apartmentSystem.apt_is_coxeter A' hA'
    obtain ⟨iso', hiso'⟩ := δW.delta_apt_compat A' hA' B_idx' M' φ' hφ'_inj hφ'_surj
    have h_DC := hiso' D C hD_A' hD_max_A' hC_A' hC_max_A'
    have h_CD := hiso' C D hC_A' hC_max_A' hD_A' hD_max_A'
    have h_anti_D : iso' (δW.delta D C) = (iso' (δW.delta C D))⁻¹ := by
      rw [h_DC, h_CD, mul_inv_rev, inv_inv]
    have h_DC_inv : δW.delta D C = (δW.delta C D)⁻¹ := by
      apply iso'.injective
      rw [h_anti_D, map_inv]
    have h_rC_inv : δW.delta (ρbar D) C = (δW.delta C (ρbar D))⁻¹ := by
      apply iso.injective
      rw [h_anti_rho, map_inv]
    rw [h_rC_inv, hρbar_delta D hD, h_DC_inv]
  · intro D₁ D₂ h_adj
    exact retraction_adj_preserves A hA ρbar hρbar_max D₁ D₂ h_adj

private lemma Building.WValuedDist.delta_injective_in_apt
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C D₁ D₂ : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC_mem : C ∈ A.faces)
  (hC : A.IsMaximal C)
  (hD₁_mem : D₁ ∈ A.faces)
  (hD₁ : A.IsMaximal D₁)
  (hD₂_mem : D₂ ∈ A.faces)
  (hD₂ : A.IsMaximal D₂)
  (h_eq : δW.delta C D₁ = δW.delta C D₂) :
-- imply
  D₁ = D₂ := by
-- proof
  obtain ⟨B_idx, M, cc, hcc_eq, φ, hφ_inj, hφ_surj, _⟩ :=
    b.apartmentSystem.apt_is_coxeter A hA
  obtain ⟨iso, hiso⟩ := δW.delta_apt_compat A hA B_idx M φ hφ_inj hφ_surj
  have h1 : iso (δW.delta C D₁) = (φ C)⁻¹ * (φ D₁) :=
    hiso C D₁ hC_mem hC hD₁_mem hD₁
  have h2 : iso (δW.delta C D₂) = (φ C)⁻¹ * (φ D₂) :=
    hiso C D₂ hC_mem hC hD₂_mem hD₂
  have h3 : (φ C)⁻¹ * (φ D₁) = (φ C)⁻¹ * (φ D₂) := by
    rw [← h1, ← h2, h_eq]
  have h4 : φ D₁ = φ D₂ := mul_left_cancel h3
  exact hφ_inj D₁ hD₁ D₂ hD₂ h4

private lemma Building.WValuedDist.folding_delta_from_center
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C : Finset V}
  {ρbar : Finset V → Finset V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → ρbar D ∈ A.faces ∧ A.IsMaximal (ρbar D))
  (hρ_fix : ∀ D, D ∈ A.faces → A.IsMaximal D → ρbar D = D)
  (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta C (ρbar D) = δW.delta C D)
  (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
  (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
  (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, δW.delta (f y₁) (f y₂) = δW.delta y₁ y₂) :
-- imply
  (∀ y ∈ Y, δW.delta C (f y) = δW.delta C y) ∧ (∀ y ∈ Y, A.IsMaximal (f y)) := by
-- proof
  have h_delta_compat : ∃ (B_idx : Type) (M : CoxeterMatrix B_idx)
    (φ : Finset V → M.Group),
    (∀ C, A.IsMaximal C → ∀ D, A.IsMaximal D → φ C = φ D → C = D) ∧
    ∃ (iso : δW.coxeterMatrix.Group ≃* M.Group),
      ∀ C D, C ∈ A.faces → A.IsMaximal C → D ∈ A.faces → A.IsMaximal D →
        iso (δW.delta C D) = (φ C)⁻¹ * (φ D) := by
    obtain ⟨B_idx, M, _, _, φ, hφ_inj, hφ_surj, _, _⟩ :=
      b.apartmentSystem.apt_is_coxeter A hA
    obtain ⟨iso, h_compat⟩ := δW.delta_apt_compat A hA B_idx M φ hφ_inj hφ_surj
    exact ⟨B_idx, M, φ, hφ_inj, iso, h_compat⟩
  have h_agree : ∀ y ∈ Y, ρbar y = f y :=
    retraction_agrees_with_delta_preserving δW.delta A hA C hC ρbar hρ_max hρ_fix hρ_delta
      Y f hY hf_img hf_delta h_delta_compat
  constructor
  · intro y hy
    rw [← h_agree y hy]
    exact hρ_delta y (hY y hy)
  · intro y hy
    rw [← h_agree y hy]
    exact (hρ_max y (hY y hy)).2

private lemma Building.WValuedDist.delta_retraction_agrees_with_iso
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {C : Finset V}
  {ρbar : Finset V → Finset V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hC : A.IsMaximal C)
  (hρ_max : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → ρbar D ∈ A.faces ∧ A.IsMaximal (ρbar D))
  (hρ_fix : ∀ D, D ∈ A.faces → A.IsMaximal D → ρbar D = D)
  (hρ_delta : ∀ D, b.toChamberComplex.toSimplicialComplex.IsMaximal D → δW.delta C (ρbar D) = δW.delta C D)
  (hY : ∀ y ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal y)
  (hf_img : ∀ y ∈ Y, f y ∈ A.faces)
  (hf_delta : ∀ y₁ ∈ Y, ∀ y₂ ∈ Y, δW.delta (f y₁) (f y₂) = δW.delta y₁ y₂) :
-- imply
  ∀ y ∈ Y, ρbar y = f y := by
-- proof
  have hfold := δW.folding_delta_from_center A hA C hC ρbar hρ_max hρ_fix hρ_delta
    Y f hY hf_img hf_delta
  have hf_delta_C : ∀ y ∈ Y, δW.delta C (f y) = δW.delta C y := hfold.1
  have hf_max : ∀ y ∈ Y, A.IsMaximal (f y) := hfold.2
  intro y hy
  have hρy := hρ_max y (hY y hy)
  have h_rho : δW.delta C (ρbar y) = δW.delta C y := hρ_delta y (hY y hy)
  have h_f : δW.delta C (f y) = δW.delta C y := hf_delta_C y hy
  have h_eq : δW.delta C (ρbar y) = δW.delta C (f y) := by
    rw [h_rho, h_f]
  exact δW.delta_injective_in_apt A hA C (ρbar y) (f y)
    hC.1 hC hρy.1 hρy.2 (hf_img y hy) (hf_max y hy) h_eq

private lemma retraction_extension_exists
  [DecidableEq V]
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
  {C' : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hf_strong : IsStrongIsometry δW Y (f '' Y) f)
  (hf_img_in_A : ∀ C ∈ Y, f C ∈ A.faces)
  (hY_chambers : ∀ C ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hC'_in_A : C' ∈ A.faces)
  (hC'_maximal : A.IsMaximal C')
  (hC'_not_in_fY : C' ∉ f '' Y)
  (_hC'_adj : ∃ D ∈ f '' Y, A.Adjacent C' D) :
-- imply
  ∃ (D' : Finset V), b.toChamberComplex.toSimplicialComplex.IsMaximal D' ∧ D' ∉ Y ∧ (∀ y ∈ Y, δW.delta (f y) C' = δW.delta y D') ∧ (∀ y ∈ Y, δW.delta C' (f y) = δW.delta D' y) ∧ δW.delta C' C' = δW.delta D' D' := by
-- proof
  obtain ⟨ρbar, hρ_max, hρ_fix, hρ_delta_from, hρ_delta_to, _hρ_adj⟩ :=
    δW.delta_retraction_preserves A hA C' hC'_maximal
  have hC'_bmax : b.toChamberComplex.toSimplicialComplex.IsMaximal C' :=
    b.apartmentSystem.maximal_in_apt_is_maximal A hA C' hC'_maximal
  have hρ_agree : ∀ y ∈ Y, ρbar y = f y :=
    δW.delta_retraction_agrees_with_iso A hA C' hC'_maximal ρbar
      hρ_max hρ_fix hρ_delta_from Y f hY_chambers hf_img_in_A hf_strong.2.2
  have hC'_not_in_Y : C' ∉ Y := by
    intro hC'_in_Y
    have h1 : ρbar C' = f C' := hρ_agree C' hC'_in_Y
    have h2 : ρbar C' = C' := hρ_fix C' hC'_in_A hC'_maximal
    have h3 : f C' = C' := by rw [← h1, h2]
    exact hC'_not_in_fY ⟨C', hC'_in_Y, h3⟩
  refine ⟨C', hC'_bmax, hC'_not_in_Y, ?_, ?_, rfl⟩
  · intro y hy
    have h := hρ_delta_to y (hY_chambers y hy)
    rwa [hρ_agree y hy] at h
  · intro y hy
    have h := hρ_delta_from y (hY_chambers y hy)
    rwa [hρ_agree y hy] at h

private lemma strong_isometry_one_step_extension
  [DecidableEq V]
  {b : Building V}
  {δW : Building.WValuedDist b}
  {A : SimplicialComplex V}
  {Y : Set (Finset V)}
  {f : Finset V → Finset V}
  {C' : Finset V}
-- given
  (hA : A ∈ b.apartmentSystem.apartments)
  (hf_strong : IsStrongIsometry δW Y (f '' Y) f)
  (hf_img_in_A : ∀ C ∈ Y, f C ∈ A.faces)
  (hY_chambers : ∀ C ∈ Y, b.toChamberComplex.toSimplicialComplex.IsMaximal C)
  (hC'_in_A : C' ∈ A.faces)
  (hC'_maximal : A.IsMaximal C')
  (hC'_not_in_fY : C' ∉ f '' Y)
  (hC'_adj : ∃ D ∈ f '' Y, A.Adjacent C' D) :
-- imply
  ∃ (g : Finset V → Finset V), IsStrongIsometry δW (f '' Y ∪ {C'}) (g '' (f '' Y ∪ {C'})) g ∧ (∀ x ∈ f '' Y, ∃ y ∈ Y, f y = x ∧ g x = y) := by
-- proof
  obtain ⟨D', hD'_max, hD'_not_in_Y, hD'_delta, hD'_delta_rev, hD'_self⟩ :=
    retraction_extension_exists δW hA hf_strong hf_img_in_A hY_chambers
      hC'_in_A hC'_maximal hC'_not_in_fY hC'_adj
  obtain ⟨hf_map, hf_surj, hf_delta⟩ := hf_strong
  have preimage_exists : ∀ x ∈ f '' Y, ∃ y ∈ Y, f y = x := hf_surj
  classical
  let g : Finset V → Finset V := fun x =>
    if x = C' then D'
    else if h : x ∈ f '' Y then (preimage_exists x h).choose
    else x
  have g_C' : g C' = D' := by simp [g]
  have g_preimage : ∀ x ∈ f '' Y, ∃ y ∈ Y, f y = x ∧ g x = y := by
    intro x hx
    have hxne : x ≠ C' := fun h => hC'_not_in_fY (h ▸ hx)
    simp only [g, hxne, ↓reduceIte, dif_pos hx]
    exact ⟨(preimage_exists x hx).choose,
      (preimage_exists x hx).choose_spec.1,
      (preimage_exists x hx).choose_spec.2, rfl⟩
  have g_in_Y : ∀ x ∈ f '' Y, g x ∈ Y := by
    intro x hx
    obtain ⟨y, hy, _, hgy⟩ := g_preimage x hx
    rw [hgy]; exact hy
  have f_g : ∀ x ∈ f '' Y, f (g x) = x := by
    intro x hx
    obtain ⟨y, _, hfy, hgy⟩ := g_preimage x hx
    rw [hgy]; exact hfy
  refine ⟨g, ⟨?_, ?_, ?_⟩, g_preimage⟩
  · intro x hx; exact Set.mem_image_of_mem g hx
  · intro z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact ⟨x, hx, rfl⟩
  · intro x₁ hx₁ x₂ hx₂
    obtain hx₁_fY | hx₁_C' := hx₁
    ·
      obtain hx₂_fY | hx₂_C' := hx₂
      ·
        have hy₁ := g_in_Y x₁ hx₁_fY
        have hy₂ := g_in_Y x₂ hx₂_fY
        have hfg₁ := f_g x₁ hx₁_fY
        have hfg₂ := f_g x₂ hx₂_fY
        rw [← hf_delta (g x₁) hy₁ (g x₂) hy₂, hfg₁, hfg₂]
      ·
        rw [Set.mem_singleton_iff.mp hx₂_C', g_C']
        have hy₁ := g_in_Y x₁ hx₁_fY
        have hfg₁ := f_g x₁ hx₁_fY
        have h := hD'_delta (g x₁) hy₁
        rwa [hfg₁] at h
    ·
      rw [Set.mem_singleton_iff.mp hx₁_C', g_C']
      obtain hx₂_fY | hx₂_C' := hx₂
      ·
        have hy₂ := g_in_Y x₂ hx₂_fY
        have hfg₂ := f_g x₂ hx₂_fY
        have h := hD'_delta_rev (g x₂) hy₂
        rwa [hfg₂] at h
      ·
        rwa [Set.mem_singleton_iff.mp hx₂_C', g_C']


-- created on 2026-10-24
