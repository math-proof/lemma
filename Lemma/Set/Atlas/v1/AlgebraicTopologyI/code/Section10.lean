import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section10.Part24
open CategoryTheory CategoryTheory.Limits AlgebraicTopologyI Set in AlgebraicTopology unitInterval ContinuousMap Excision SphereHomology BrouwerFixedPoint BrouwerFixedPoint.ExcisionApplications BrouwerFixedPoint.DegreeTheory
open AlgebraicTopology
open AlgebraicTopology Set
open Metric Set Inner
open Set Topology EilenbergSteenrod DeformationRetract
open AlgebraicTopology CategoryTheory


namespace Excision

/--
[cover_of_excisive](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma cover_of_excisive
  {X : Type}
  [TopologicalSpace X]
  {A U : Set X}
-- given
  (hexc : IsExcisive X A U) :
-- imply
  interior A ∪ interior Uᶜ = Set.univ := by
-- proof
  rw [Set.eq_univ_iff_forall]
  intro x
  by_cases hx : x ∈ interior A
  · exact Set.mem_union_left _ hx
  · refine Set.mem_union_right _ ?_
    rw [interior_compl]
    exact fun hcl => hx (hexc hcl)

end Excision

namespace Excision

/--
[twoElementCover_isCover](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma twoElementCover_isCover
  {X : Type}
  [TopologicalSpace X]
  {A B : Set X}
-- given
  (hcover : interior A ∪ interior B = Set.univ) :
-- imply
  IsCover ({A, B} : Set (Set X)) := by
-- proof
  rw [isCover_iff]
  intro x
  have hx := eq_univ_iff_forall.mp hcover x
  obtain hA | hB := hx
  · exact ⟨A, Or.inl rfl, hA⟩
  · exact ⟨B, Or.inr (mem_singleton_iff.mpr rfl), hB⟩

end Excision

namespace Excision

/--
[topSES_shortExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma topSES_shortExact
  {X : Type}
  [TopologicalSpace X]
  {A B : Set X} :
-- imply
  (topSES X A B).ShortExact :=
-- proof
  { exact := ShortComplex.exact_cokernel _ }

end Excision

namespace Excision

/--
[thirdIso_shortExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma thirdIso_shortExact
  {A B C : ChainComplex AddCommGrpCat ℕ}
  {f : A ⟶ B}
  {g : B ⟶ C}
  [Mono f]
  [Mono g]
  [Mono (f ≫ g)] :
-- imply
  (ShortComplex.mk (cokernel.map f (f ≫ g) (𝟙 A) g (by simp)) (cokernel.map (f ≫ g) g f (𝟙 C) (by simp)) (by apply (cancel_epi (cokernel.π f)).mp simp only [comp_zero, cokernel.π_desc_assoc, Category.assoc, cokernel.π_desc, Category.id_comp, cokernel.condition])).ShortExact where exact :=
-- proof
  (kernelCokernelCompSequence_exact f g).exact 3
    mono_f := by
      have sq : IsPullback f (𝟙 A) g (f ≫ g) :=
        IsPullback.of_vert_isIso_mono ⟨by simp⟩
      exact Abelian.mono_cokernel_map_of_isPullback sq
    epi_g := by
      suffices h : Epi (cokernel.π (f ≫ g) ≫ cokernel.map (f ≫ g) g f (𝟙 C) (by simp)) from
        epi_of_epi (cokernel.π (f ≫ g)) _
      rw [cokernel.π_desc]
      infer_instance
section SecondIsoAbstract
variable {𝒞 : Type*} [Category 𝒞] [Abelian 𝒞]
  {𝒜 ℬ 𝒳 : 𝒞} (φ : 𝒜 ⟶ 𝒳) (ψ : ℬ ⟶ 𝒳)
set_option linter.unusedSectionVars false in

end Excision

namespace SphereHomology

/--
[isZero_SHG_contractible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma isZero_SHG_contractible
  {X : Type}
  [TopologicalSpace X]
  [ContractibleSpace X]
  {k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  IsZero ((singularChainZF.obj (TopCat.of X)).homology k) := by
-- proof
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  let F := singularChainZF ⋙ HomologicalComplex.homologyFunctor _ _ k
  have hmap : F.map (𝟙 (TopCat.of X)) = F.map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show F.map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (show TopCat.Homotopy _ _ from Hx).congr_homologyMap_singularChainComplexFunctor
      (AddCommGrpCat.of ℤ) k
  rw [F.map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q' : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q' := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, F.map_comp] at hmap
  have hpz : IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk
  have : F.map p ≫ F.map q' = 0 := by
    rw [hpz.eq_of_src (F.map q') 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap

end SphereHomology

/--
[suspIsZero_SHG_contractible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma suspIsZero_SHG_contractible
  {X : Type}
  [TopologicalSpace X]
  [ContractibleSpace X]
  {k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  IsZero ((suspSingularChainZF.obj (TopCat.of X)).homology k) := by
-- proof
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  let F := suspSingularChainZF ⋙ HomologicalComplex.homologyFunctor _ _ k
  have hmap : F.map (𝟙 (TopCat.of X)) = F.map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show F.map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (show TopCat.Homotopy _ _ from Hx).congr_homologyMap_singularChainComplexFunctor
      (AddCommGrpCat.of ℤ) k
  rw [F.map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q' : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q' := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, F.map_comp] at hmap
  have hpz : IsZero (F.obj (TopCat.of PUnit)) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ _ _ _ hk
  have : F.map p ≫ F.map q' = 0 := by
    rw [hpz.eq_of_src (F.map q') 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap

/--
[sphere_zero_homology_vanishing](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma sphere_zero_homology_vanishing
  {q : ℕ}
-- given
  (hq : q > 0) :
-- imply
  IsZero (SingularHomologyGroup q (Sphere 0)) := by
-- proof
  open AlgebraicTopology in
  exact isZero_singularHomologyFunctor_of_totallyDisconnectedSpace _ q _ _ (by omega)

/--
[sphere_zero_homology_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma sphere_zero_homology_zero
-- imply
  Nonempty (SingularHomologyGroup 0 (Sphere 0) ≅ AddCommGrpCat.of (ℤ × ℤ)) := by
-- proof
  classical
  let step1 := singularHomologyFunctorZeroOfTotallyDisconnectedSpace
    AddCommGrpCat (AddCommGrpCat.of ℤ) (TopCat.of (Sphere 0))
  let f : Sphere 0 → AddCommGrpCat.{0} := fun _ => AddCommGrpCat.of ℤ
  let step2 := (biproduct.isoCoproduct f).symm
  let step3 := AddCommGrpCat.biproductIsoPi f
  have hp1 : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ)) ∈
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq,
      Fin.sum_univ_one]
    simp [Real.sqrt_sq_eq_abs]
  have hp2 : (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ)) ∈
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 1)) 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, EuclideanSpace.norm_eq,
      Fin.sum_univ_one]
    simp [Real.sqrt_sq_eq_abs]
  let p1 : Sphere 0 := ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ)), hp1⟩
  let p2 : Sphere 0 := ⟨(EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ)), hp2⟩
  have hp1_ne_p2 : p1 ≠ p2 := by
    intro h
    have h' := Subtype.ext_iff.mp h
    have h'' := congr_arg (fun x : EuclideanSpace ℝ (Fin 1) => x 0) h'
    dsimp [p1, p2] at h''
    linarith
  have hcard : ∀ x : Sphere 0, x = p1 ∨ x = p2 := by
    intro ⟨x, hx⟩
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hx
    have hn := EuclideanSpace.norm_eq x
    rw [hx] at hn
    rw [Fin.sum_univ_one, Real.sqrt_sq (norm_nonneg _)] at hn
    have habsx : x.ofLp 0 = 1 ∨ x.ofLp 0 = -1 := by
      rw [Real.norm_eq_abs] at hn
      exact abs_eq (by norm_num : (1 : ℝ) ≥ 0) |>.mp hn.symm
    obtain h | h := habsx
    · left; apply Subtype.ext; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p1]
    · right; apply Subtype.ext; ext i; fin_cases i; show x.ofLp 0 = _; rw [h]; simp [p2]
  let piEquiv : (∀ _ : Sphere 0, ℤ) ≃+ ℤ × ℤ :=
    { toFun := fun g => (g p1, g p2)
      invFun := fun p x => if x = p1 then p.1 else p.2
      left_inv := by
        intro g; ext x
        obtain rfl | rfl := hcard x
        · simp
        · have : p2 ≠ p1 := Ne.symm hp1_ne_p2
          simp [this]
      right_inv := by
        intro ⟨a, b⟩
        have : p2 ≠ p1 := Ne.symm hp1_ne_p2
        simp [this]
      map_add' := fun _ _ => rfl }
  let step4 : AddCommGrpCat.of (∀ _ : Sphere 0, ℤ) ≅ AddCommGrpCat.of (ℤ × ℤ) :=
    piEquiv.toAddCommGrpIso
  exact ⟨step1 ≪≫ step2 ≪≫ step3 ≪≫ step4⟩

/--
[addCommGrpCat_int_not_isZero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma addCommGrpCat_int_not_isZero
-- imply
  ¬ IsZero (AddCommGrpCat.of ℤ) := by
-- proof
  intro h
  have heq := h.eq_of_src (𝟙 (AddCommGrpCat.of ℤ)) 0
  have h1 := congrArg (fun f => (CategoryTheory.ConcreteCategory.hom f) (1 : ℤ)) heq
  simp at h1

/--
[punctured_euclidean_homotopyEquiv_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma punctured_euclidean_homotopyEquiv_sphere
  {n : ℕ} :
-- imply
  Nonempty ({x : EuclideanSpace ℝ (Fin (n + 1)) | x ≠ 0} ≃ₕ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) := by
-- proof
  open unitInterval ContinuousMap in
  let E := EuclideanSpace ℝ (Fin (n + 1))
  have coeff_pos : ∀ (t : I) (x : E), x ≠ 0 →
    0 < (1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ) := by
    intro t x hx
    have ht0 := unitInterval.nonneg t
    have hnp : (0 : ℝ) < ‖x‖ := norm_pos_iff.mpr hx
    obtain heq | htpos := eq_or_lt_of_le ht0
    · rw [← heq]; simp [inv_pos.mpr hnp]
    · exact add_pos_of_nonneg_of_pos
      (mul_nonneg (by linarith [unitInterval.le_one t]) (inv_nonneg.mpr hnp.le)) htpos
  have coeff_ne : ∀ (t : I) (x : E), x ≠ 0 →
    (1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ) ≠ 0 :=
    fun t x hx => ne_of_gt (coeff_pos t x hx)
  let r : C({x : E | x ≠ 0}, Metric.sphere (0 : E) 1) :=
    ⟨fun ⟨x, hx⟩ => ⟨(‖x‖⁻¹ : ℝ) • x, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero]
      exact norm_smul_inv_norm (𝕜 := ℝ) hx⟩,
    Continuous.subtype_mk
      (((continuous_norm.comp continuous_subtype_val).inv₀
        (fun ⟨_, hx⟩ => norm_ne_zero_iff.mpr hx)).smul continuous_subtype_val) _⟩
  let i : C(Metric.sphere (0 : E) 1, {x : E | x ≠ 0}) :=
    ⟨fun ⟨y, hy⟩ => ⟨y, by
      rw [Metric.mem_sphere, dist_eq_norm, sub_zero] at hy
      intro h0; simp [h0] at hy⟩,
    continuous_subtype_val.subtype_mk _⟩
  have ri_eq_id : r.comp i = ContinuousMap.id _ := by
    ext1 ⟨y, hy⟩
    simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, ContinuousMap.id_apply, r, i]
    ext1
    have hny : ‖y‖ = 1 := by rwa [Metric.mem_sphere, dist_eq_norm, sub_zero] at hy
    simp [hny]
  have ir_htpy_id : (i.comp r).Homotopic (ContinuousMap.id _) := by
    refine ⟨⟨⟨fun ⟨t, ⟨x, hx⟩⟩ =>
      ⟨((1 - (t : ℝ)) * ‖x‖⁻¹ + (t : ℝ)) • x, ?nonzero⟩, ?cont⟩, ?zero, ?one⟩⟩
    case nonzero =>
      intro h
      obtain h1 | h2 := eq_zero_or_eq_zero_of_smul_eq_zero h
      · exact absurd h1 (coeff_ne t x hx)
      · exact hx h2
    case cont =>
      apply Continuous.subtype_mk
      exact (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
        ((continuous_norm.comp (continuous_subtype_val.comp continuous_snd)).inv₀
          (fun ⟨_, ⟨_, hx⟩⟩ => norm_ne_zero_iff.mpr hx))).add
        (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd)
    case zero =>
      intro ⟨x, hx⟩
      ext1
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, r, i]
      have h0 : (↑(0 : I) : ℝ) = 0 := rfl
      rw [h0]
      simp
    case one =>
      intro ⟨x, hx⟩
      ext1
      simp only [ContinuousMap.id_apply]
      have h1 : (↑(1 : I) : ℝ) = 1 := rfl
      rw [h1]
      simp
  exact ⟨⟨r, i, ir_htpy_id, ri_eq_id ▸ Homotopic.refl _⟩⟩

namespace BrouwerFixedPoint

/--
[isZero_homology_of_contractible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma isZero_homology_of_contractible
  {X : Type}
  [TopologicalSpace X]
  [ContractibleSpace X]
  {k : ℕ}
-- given
  (hk : k ≠ 0) :
-- imply
  IsZero ((homFunctorZ k).obj (TopCat.of X)) := by
-- proof
  obtain ⟨x₀, ⟨Hx⟩⟩ := (contractible_iff_id_nullhomotopic X).mp ‹_›
  have hmap : (homFunctorZ k).map (𝟙 (TopCat.of X)) =
    (homFunctorZ k).map (TopCat.ofHom (ContinuousMap.const X x₀)) := by
    show (homFunctorZ k).map (TopCat.ofHom (ContinuousMap.id X)) = _
    exact (Hx : TopCat.Homotopy _ _).congr_homologyMap_singularChainComplexFunctor _ _
  rw [(homFunctorZ k).map_id] at hmap
  let p : TopCat.of X ⟶ TopCat.of PUnit := TopCat.ofHom ⟨fun _ => .unit, continuous_const⟩
  let q : TopCat.of PUnit ⟶ TopCat.of X := TopCat.ofHom ⟨fun _ => x₀, continuous_const⟩
  have hfact : TopCat.ofHom (ContinuousMap.const X x₀) = p ≫ q := by
    apply TopCat.hom_ext; apply ContinuousMap.ext; intro _; rfl
  rw [hfact, (homFunctorZ k).map_comp] at hmap
  have : (homFunctorZ k).map p ≫ (homFunctorZ k).map q = 0 := by
    rw [(AlgebraicTopology.isZero_singularHomologyFunctor_of_totallyDisconnectedSpace
      _ _ _ _ hk).eq_of_src ((homFunctorZ k).map q) 0, comp_zero]
  rw [this] at hmap
  exact (IsZero.iff_id_eq_zero _).mpr hmap

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[sphereInclusion_diskRetraction](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma sphereInclusion_diskRetraction
  {n : ℕ}
  {r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
-- given
  (hr : IsRetraction n r) :
-- imply
  sphereInclusion n ≫ diskRetraction n r hr = 𝟙 _ := by
-- proof
  apply TopCat.hom_ext; apply ContinuousMap.ext
  intro ⟨x, hx⟩
  show (⟨r x, _⟩ : ↥(Sphere n)) = ⟨x, hx⟩
  exact Subtype.ext (hr.fixes_boundary x hx)

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[not_isZero_of_nontrivial](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma not_isZero_of_nontrivial
  {G : Type*}
  [AddCommGroup G]
  [Nontrivial G] :
-- imply
  ¬ IsZero (AddCommGrpCat.of G) := by
-- proof
  intro h
  obtain ⟨a, b, hab⟩ := exists_pair_ne (α := G)
  have ha : a = (0 : G) := by
    have := congrArg (fun f => AddCommGrpCat.Hom.hom f a) ((IsZero.iff_id_eq_zero _).mp h)
    simpa using this
  have hb : b = (0 : G) := by
    have := congrArg (fun f => AddCommGrpCat.Hom.hom f b) ((IsZero.iff_id_eq_zero _).mp h)
    simpa using this
  exact hab (by rw [ha, hb])

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[norm_fin1_eq_abs_coord](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma norm_fin1_eq_abs_coord
  {x : EuclideanSpace ℝ (Fin 1)} :
-- imply
  ‖x‖ = := by
-- proof
  simp [EuclideanSpace.norm_eq, coordProj, EuclideanSpace.proj,
    Finset.sum_singleton, Real.sqrt_sq_eq_abs, sq_abs]

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[no_retraction_dim_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma no_retraction_dim_one
  {r : EuclideanSpace ℝ (Fin 1) → EuclideanSpace ℝ (Fin 1)}
-- given
  (hr : IsRetraction 1 r) :
-- imply
  False := by
-- proof
  set g := (coordProj ·) ∘ r
  have hg_cont : Continuous g := coordProj.continuous.comp hr.continuous_r
  have hg_pm : ∀ x ∈ Disk 1, g x = 1 ∨ g x = -1 := by
    intro x hx
    have hmem := hr.maps_to x hx
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord] at hmem
    change coordProj (r x) = 1 ∨ coordProj (r x) = -1
    cases abs_cases (coordProj (r x)) with
    | inl h => left; linarith [h.1]
    | inr h => right; linarith [h.1]
  set epos : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (1 : ℝ))
  set eneg : EuclideanSpace ℝ (Fin 1) := (EuclideanSpace.equiv (Fin 1) ℝ).symm (fun _ => (-1 : ℝ))
  have hepos_sph : epos ∈ Sphere 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord]
    simp [coordProj, EuclideanSpace.proj, epos]
  have heneg_sph : eneg ∈ Sphere 1 := by
    rw [Metric.mem_sphere, dist_eq_norm, sub_zero, norm_fin1_eq_abs_coord]
    simp [coordProj, EuclideanSpace.proj, eneg]
  have hg_epos : g epos = 1 := by
    show coordProj (r epos) = 1
    rw [hr.fixes_boundary epos hepos_sph]
    simp [coordProj, EuclideanSpace.proj, epos]
  have hg_eneg : g eneg = -1 := by
    show coordProj (r eneg) = -1
    rw [hr.fixes_boundary eneg heneg_sph]
    simp [coordProj, EuclideanSpace.proj, eneg]
  obtain ⟨x, hx, hgx⟩ := (convex_closedBall (0 : EuclideanSpace ℝ (Fin 1)) 1).isPreconnected
    |>.intermediate_value₂
    (Metric.sphere_subset_closedBall heneg_sph) (Metric.sphere_subset_closedBall hepos_sph)
    hg_cont.continuousOn continuousOn_const
    (by rw [hg_eneg]; norm_num : g eneg ≤ 0) (by rw [hg_epos]; norm_num : (0 : ℝ) ≤ g epos)
  obtain h | h <;> linarith := hg_pm x hx

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[projBall_continuous](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma projBall_continuous
  {n : ℕ} :
-- imply
  Continuous (projBall : EuclideanSpace ℝ (Fin n) → _) :=
-- proof
  (((continuous_const.max continuous_norm).inv₀
    (fun x => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left 1 ‖x‖)))).smul continuous_id)

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[projBall_mem_disk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma projBall_mem_disk
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)} :
-- imply
  projBall x ∈ Disk n := by
-- proof
  simp only [Disk, mem_closedBall, dist_zero_right, projBall, norm_smul]
  have hmax : (0 : ℝ) < max 1 ‖x‖ := lt_of_lt_of_le one_pos (le_max_left 1 ‖x‖)
  rw [Real.norm_of_nonneg (inv_nonneg.mpr hmax.le), inv_mul_le_iff₀ hmax]
  linarith [le_max_right 1 ‖x‖]

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[projBall_eq_of_mem_disk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma projBall_eq_of_mem_disk
  {n : ℕ}
  {x : EuclideanSpace ℝ (Fin n)}
-- given
  (hx : x ∈ Disk n) :
-- imply
  projBall x = x := by
-- proof
  simp only [Disk, mem_closedBall, dist_zero_right] at hx
  simp only [projBall, max_eq_left hx, inv_one, one_smul]

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[quadratic_ray_root](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma quadratic_ray_root
  {c β s α : ℝ}
-- given
  (hc : c ≠ 0)
  (hs : s ^ 2 = β ^ 2 + c * (1 - α)) :
-- imply
  c * ((-β + s) / c) ^ 2 + 2 * β * ((-β + s) / c) + α = 1 := by
-- proof
  field_simp
  nlinarith [sq_nonneg (c * α), sq_nonneg s, sq_nonneg β, sq_nonneg c]

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[retractionMap_norm_eq_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma retractionMap_norm_eq_one
  {n : ℕ}
  {a v : EuclideanSpace ℝ (Fin n)}
-- given
  (ha : ‖a‖ ≤ 1)
  (hv : v ≠ 0) :
-- imply
  ‖a + rayParam a v • v‖ = 1 := by
-- proof
  show ‖a + ((-inner (𝕜 := ℝ) a v + Real.sqrt (rayDiscrim a v)) / ‖v‖ ^ 2) • v‖ = 1
  show ‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) / ‖v‖ ^ 2) • v‖ = 1
  have hv_norm : ‖v‖ ≠ 0 := by simp [hv]
  have hv2 : ‖v‖ ^ 2 ≠ 0 := pow_ne_zero 2 hv_norm
  have hΔ : 0 ≤ inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2) := by
    apply add_nonneg (sq_nonneg _)
    exact mul_nonneg (sq_nonneg _) (by linarith [(sq_le_one_iff₀ (norm_nonneg a)).mpr ha])
  have key := quadratic_ray_root (‖v‖ ^ 2) (inner (𝕜 := ℝ) a v)
    (Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2)))
    (‖a‖ ^ 2) hv2 (Real.sq_sqrt hΔ)
  have norm_sq : ‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v‖ ^ 2 = 1 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow,
      Real.norm_eq_abs, sq_abs]; linarith
  nlinarith [sq_nonneg (‖a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v‖ - 1),
    norm_nonneg (a + ((-inner (𝕜 := ℝ) a v +
    Real.sqrt (inner (𝕜 := ℝ) a v ^ 2 + ‖v‖ ^ 2 * (1 - ‖a‖ ^ 2))) /
    ‖v‖ ^ 2) • v)]

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[rayParam_eq_one_of_norm_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma rayParam_eq_one_of_norm_one
  {n : ℕ}
  {a x : EuclideanSpace ℝ (Fin n)}
-- given
  (ha : ‖a‖ ≤ 1)
  (hx : ‖x‖ = 1)
  (hne : a ≠ x) :
-- imply
  rayParam a (x - a) = 1 := by
-- proof
  unfold rayParam rayDiscrim
  have hv : x - a ≠ 0 := sub_ne_zero.mpr hne.symm
  have hv2_pos : 0 < ‖x - a‖ ^ 2 := by
    have : 0 < ‖x - a‖ := norm_pos_iff.mpr hv; positivity
  suffices h : -inner (𝕜 := ℝ) a (x - a) +
    Real.sqrt (inner (𝕜 := ℝ) a (x - a) ^ 2 +
      ‖x - a‖ ^ 2 * (1 - ‖a‖ ^ 2)) = ‖x - a‖ ^ 2 by
    rw [h, div_self (ne_of_gt hv2_pos)]
  have hinner : (inner (𝕜 := ℝ) a (x - a) : ℝ) = inner (𝕜 := ℝ) a x - ‖a‖ ^ 2 := by
    simp only [inner_sub_right, real_inner_self_eq_norm_sq]
  have hnorm_v : ‖x - a‖ ^ 2 = 1 - 2 * (inner (𝕜 := ℝ) a x : ℝ) + ‖a‖ ^ 2 := by
    rw [norm_sub_sq_real, hx, one_pow, real_inner_comm]
  have hDiscrim : (inner (𝕜 := ℝ) a (x - a)) ^ 2 + ‖x - a‖ ^ 2 * (1 - ‖a‖ ^ 2) =
    (1 - (inner (𝕜 := ℝ) a x : ℝ)) ^ 2 := by
    rw [hinner, hnorm_v]; ring
  have hβ_le : (inner (𝕜 := ℝ) a x : ℝ) ≤ 1 := by
    calc _ ≤ ‖a‖ * ‖x‖ := real_inner_le_norm a x
    _ = ‖a‖ := by rw [hx, mul_one]
    _ ≤ 1 := ha
  rw [hDiscrim, Real.sqrt_sq (by linarith), hinner, hnorm_v]; ring

end BrouwerFixedPoint

namespace BrouwerFixedPoint

/--
[retraction_of_fixed_point_free](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma retraction_of_fixed_point_free
  {n : ℕ}
  {f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)}
-- given
  (_hn : 0 < n)
  (hf_cont : Continuous f)
  (hf_maps : ∀ x, x ∈ Disk n → f x ∈ Disk n)
  (hf_no_fp : ∀ x, x ∈ Disk n → f x ≠ x) :
-- imply
  ∃ r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n), IsRetraction n r := by
-- proof
  let r : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
    fun x => retractionMap f (projBall x)
  have hp_disk : ∀ x, projBall (n := n) x ∈ Disk n := projBall_mem_disk n
  have hv_ne : ∀ x, projBall (n := n) x - f (projBall x) ≠ 0 :=
    fun x => sub_ne_zero.mpr (Ne.symm (hf_no_fp _ (hp_disk x)))
  refine ⟨r, ⟨?_, ?_, ?_⟩⟩
  ·
    show Continuous r
    simp only [r, retractionMap, rayParam, rayDiscrim]
    have hp : Continuous (projBall : EuclideanSpace ℝ (Fin n) → _) := projBall_continuous n
    have ha : Continuous (fun x => f (projBall (n := n) x)) := hf_cont.comp hp
    have hv : Continuous (fun x => projBall (n := n) x - f (projBall x)) := hp.sub ha
    have hinner : Continuous (fun x =>
      (inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x)) : ℝ)) :=
      continuous_inner.comp (ha.prodMk hv)
    have hnv2 : Continuous (fun x => ‖projBall (n := n) x - f (projBall x)‖ ^ 2) :=
      (continuous_norm.comp hv).pow 2
    have hna2 : Continuous (fun x => ‖f (projBall (n := n) x)‖ ^ 2) :=
      (continuous_norm.comp ha).pow 2
    have hdisc : Continuous (fun x =>
      (inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) ^ 2 +
      ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
        (1 - ‖f (projBall (n := n) x)‖ ^ 2)) :=
      (hinner.pow 2).add (hnv2.mul (continuous_const.sub hna2))
    have hsqrt : Continuous (fun x => Real.sqrt (
      (inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) ^ 2 +
      ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
        (1 - ‖f (projBall (n := n) x)‖ ^ 2))) :=
      Real.continuous_sqrt.comp hdisc
    have hnum : Continuous (fun x =>
      -(inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) +
      Real.sqrt ((inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) ^ 2 +
      ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
        (1 - ‖f (projBall (n := n) x)‖ ^ 2))) :=
      hinner.neg.add hsqrt
    have ht : Continuous (fun x =>
      (-(inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) +
      Real.sqrt ((inner (𝕜 := ℝ) (f (projBall (n := n) x))
        (projBall x - f (projBall x))) ^ 2 +
      ‖projBall (n := n) x - f (projBall x)‖ ^ 2 *
        (1 - ‖f (projBall (n := n) x)‖ ^ 2))) /
      ‖projBall (n := n) x - f (projBall x)‖ ^ 2) :=
      hnum.div hnv2 (fun x => pow_ne_zero 2 (by
        have := hv_ne x
        simp only [ne_eq, norm_eq_zero] at this ⊢; exact this))
    exact ha.add (ht.smul hv)
  ·
    intro x hx
    show retractionMap f (projBall x) ∈ Sphere n
    rw [projBall_eq_of_mem_disk n hx]
    simp only [retractionMap, Sphere, mem_sphere, dist_zero_right]
    exact retractionMap_norm_eq_one
      (by have := hf_maps x hx; simp only [Disk, mem_closedBall, dist_zero_right] at this; exact this)
      (sub_ne_zero.mpr (Ne.symm (hf_no_fp x hx)))
  ·
    intro x hx
    show retractionMap f (projBall x) = x
    rw [projBall_eq_of_mem_disk n (sphere_subset_closedBall hx)]
    simp only [retractionMap]
    rw [rayParam_eq_one_of_norm_one
      (by have := hf_maps x (sphere_subset_closedBall hx)
        simp only [Disk, mem_closedBall, dist_zero_right] at this; exact this)
      (by simp only [Sphere, mem_sphere, dist_zero_right] at hx; exact hx)
      (hf_no_fp x (sphere_subset_closedBall hx)),
      one_smul]
    abel
/-- **Theorem 10.7 (Brouwer fixed-point theorem).** Every continuous self-map
`f : D^n → D^n` of the closed unit disk in `ℝ^n` (for `n ≥ 1`) has a fixed point. The
proof: a fixed-point-free `f` would yield a retraction `D^n → S^{n-1}`, contradicting
`no_retraction_disk_to_sphere`. -/
end BrouwerFixedPoint
namespace ExcisionApplications
open Set Topology EilenbergSteenrod DeformationRetract
universe u


namespace ExcisionApplications

/--
[mapOfPairs_ext](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma mapOfPairs_ext
  {X : Type u}
  [TopologicalSpace X]
  {P Q : TopPair}
  {f g : MapOfPairs P Q}
-- given
  (h : f.toFun = g.toFun) :
-- imply
  f = g := by
-- proof
  cases f; cases g; congr

end ExcisionApplications

namespace ExcisionApplications

/--
[excisionInclusion_comp_subspacePairToExcisePair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma excisionInclusion_comp_subspacePairToExcisePair
  {X : Type u}
  [TopologicalSpace X]
  {A B : Set X} :
-- imply
  (excisionInclusion ⟨X, inferInstance, A⟩ Bᶜ).comp (subspacePairToExcisePair A B) = pairInclusion A B :=
-- proof
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

end ExcisionApplications

namespace ExcisionApplications

/--
[roundTrip_subspacePair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma roundTrip_subspacePair
  {X : Type u}
  [TopologicalSpace X]
  {A B : Set X} :
-- imply
  (excisePairToSubspacePair A B).comp (subspacePairToExcisePair A B) = MapOfPairs.id (subspacePair A B) :=
-- proof
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

end ExcisionApplications

namespace ExcisionApplications

/--
[roundTrip_excisePair](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma roundTrip_excisePair
  {X : Type u}
  [TopologicalSpace X]
  {A B : Set X} :
-- imply
  (subspacePairToExcisePair A B).comp (excisePairToSubspacePair A B) = MapOfPairs.id ((⟨X, inferInstance, A⟩ : TopPair).excisePair Bᶜ) :=
-- proof
  mapOfPairs_ext (funext fun ⟨_, _⟩ => rfl)

end ExcisionApplications

namespace ExcisionApplications

/--
[subsingleton_relative_of_inclusionBijective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma subsingleton_relative_of_inclusionBijective
  {X : Type u}
  [TopologicalSpace X]
  {P : TopPair}
  {n : ℤ}
-- given
  (h : HomologyTheory.{u})
  (hbij : ∀ m : ℤ, Function.Bijective (h.map m (inclusionSubToSpace P))) :
-- imply
  Subsingleton (h.H (n + 1) P) := by
-- proof
  have h_i_surj : Function.Surjective (h.map (n + 1) (inclusionSubToSpace P)) :=
    (hbij (n + 1)).2
  have hexact_space := h.exact_at_space (n + 1) P
  have hj_zero : ∀ x, h.map (n + 1) (inclusionSpaceToPair P) x = 0 := fun x =>
    (hexact_space x).mpr (h_i_surj.range_eq ▸ Set.mem_univ x)
  have h_i_inj : Function.Injective (h.map n (inclusionSubToSpace P)) := (hbij n).1
  have hexact_sub := h.exact_at_sub n P
  have h_bnd_zero : ∀ (y : h.H (n + 1) P), h.boundary n P y = 0 := by
    intro y
    have h_in_im : h.boundary n P y ∈ Set.range (h.boundary n P) := ⟨y, rfl⟩
    have h_ker : (h.map n (inclusionSubToSpace P)) (h.boundary n P y) = 0 :=
      (hexact_sub (h.boundary n P y)).mpr h_in_im
    exact h_i_inj (h_ker.trans (map_zero _).symm)
  have hexact_pair := h.exact_at_pair n P
  constructor
  intro x y
  have hx_range : x ∈ Set.range (h.map (n + 1) (inclusionSpaceToPair P)) :=
    (hexact_pair x).mp (h_bnd_zero x)
  have hy_range : y ∈ Set.range (h.map (n + 1) (inclusionSpaceToPair P)) :=
    (hexact_pair y).mp (h_bnd_zero y)
  obtain ⟨x', hx'⟩ := hx_range
  obtain ⟨y', hy'⟩ := hy_range
  rw [← hx', ← hy', hj_zero x', hj_zero y']

end ExcisionApplications

namespace ExcisionApplications

/--
[subsingleton_relative_of_inclusionBijective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma subsingleton_relative_of_inclusionBijective'
  {X : Type u}
  [TopologicalSpace X]
  {P : TopPair}
  {m : ℤ}
-- given
  (h : HomologyTheory.{u})
  (hbij : ∀ m : ℤ, Function.Bijective (h.map m (inclusionSubToSpace P))) :
-- imply
  Subsingleton (h.H m P) := by
-- proof
  have hm : m = (m - 1) + 1 := (Int.sub_add_cancel m 1).symm
  rw [hm]
  exact subsingleton_relative_of_inclusionBijective h P hbij (m - 1)
/-- If `S ⊆ Y` is a deformation retract of `Y`, then the inclusion `S ↪ Y` induces an
isomorphism on homology in every degree (homotopy invariance applied to the retraction). -/
end ExcisionApplications
noncomputable section
open AlgebraicTopology CategoryTheory
namespace DegreeTheory

end ExcisionApplications

namespace DegreeTheory

/--
[degreeOfEndo_eq_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma degreeOfEndo_eq_smul
  {G : AddCommGrpCat}
  {φ : G ≅ AddCommGrpCat.of ℤ}
  {e : G ⟶ G}
  {x : ℤ} :
-- imply
  (φ.inv ≫ e ≫ φ.hom) x = degreeOfEndo φ e * x :=
-- proof
  addCommGrpCat_endZ_apply (φ.inv ≫ e ≫ φ.hom) x

end DegreeTheory

namespace DegreeTheory

/--
[degreeOfEndo_iso_independent](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma degreeOfEndo_iso_independent
  {G : AddCommGrpCat}
  {φ φ' : G ≅ AddCommGrpCat.of ℤ}
  {e : G ⟶ G} :
-- imply
  degreeOfEndo φ e = degreeOfEndo φ' e := by
-- proof
  simp only [degreeOfEndo]
  set σ := φ.symm ≪≫ φ'
  have hφ'_hom : φ'.hom = φ.hom ≫ σ.hom := by
    simp [σ, Iso.trans, Iso.symm]
  have hφ'_inv : φ'.inv = σ.inv ≫ φ.inv := by
    simp [σ, Iso.trans, Iso.symm]
  rw [hφ'_inv, hφ'_hom]
  simp only [Category.assoc]
  change (ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1 =
    (ConcreteCategory.hom σ.hom)
      ((ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom))
        ((ConcreteCategory.hom σ.inv) 1))
  rw [addCommGrpCat_endZ_apply (φ.inv ≫ e ≫ φ.hom) ((ConcreteCategory.hom σ.inv) 1)]
  rw [show (ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1 *
    (ConcreteCategory.hom σ.inv) 1 =
    ((ConcreteCategory.hom (φ.inv ≫ e ≫ φ.hom)) 1) •
    ((ConcreteCategory.hom σ.inv) 1) from by ring]
  rw [(ConcreteCategory.hom σ.hom).map_zsmul]
  have hσ : (ConcreteCategory.hom σ.hom) ((ConcreteCategory.hom σ.inv) 1) = (1 : ℤ) := by
    change (ConcreteCategory.hom (σ.inv ≫ σ.hom)) 1 = 1
    simp [Iso.inv_hom_id]
  rw [hσ]; simp [mul_one]

end DegreeTheory

namespace DegreeTheory

/--
[degreeOfEndo_conj](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma degreeOfEndo_conj
  {G H : AddCommGrpCat}
  {φ : G ≅ AddCommGrpCat.of ℤ}
  {ψ : H ≅ AddCommGrpCat.of ℤ}
  {α : G ≅ H}
  {e : G ⟶ G} :
-- imply
  degreeOfEndo ψ (α.inv ≫ e ≫ α.hom) = degreeOfEndo φ e := by
-- proof
  have h : degreeOfEndo ψ (α.inv ≫ e ≫ α.hom) = degreeOfEndo (α ≪≫ ψ) e := by
    simp only [degreeOfEndo, Iso.trans_hom, Iso.trans_inv, Category.assoc]
  rw [h]
  exact degreeOfEndo_iso_independent (α ≪≫ ψ) φ e

end DegreeTheory

namespace DegreeTheory

/--
[addCommGrpCat_endZ_eq_of_apply_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma addCommGrpCat_endZ_eq_of_apply_one
  {e₁ e₂ : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ}
-- given
  (h : (ConcreteCategory.hom e₁) (1 : ℤ) = (ConcreteCategory.hom e₂) (1 : ℤ)) :
-- imply
  e₁ = e₂ := by
-- proof
  apply ConcreteCategory.hom_ext
  intro x
  have h1 := (ConcreteCategory.hom e₁).map_zsmul 1 x
  have h2 := (ConcreteCategory.hom e₂).map_zsmul 1 x
  simp only [smul_eq_mul, mul_one] at h1 h2
  rw [h1, h2, h]

end DegreeTheory

namespace DegreeTheory

/--
[endo_eq_of_same_degree'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
lemma endo_eq_of_same_degree'
  {G : AddCommGrpCat}
  {φ : G ≅ AddCommGrpCat.of ℤ}
  {e₁ e₂ : G ⟶ G}
-- given
  (h : degreeOfEndo φ e₁ = degreeOfEndo φ e₂) :
-- imply
  e₁ = e₂ := by
-- proof
  have key : φ.inv ≫ e₁ ≫ φ.hom = φ.inv ≫ e₂ ≫ φ.hom :=
    addCommGrpCat_endZ_eq_of_apply_one _ _ h
  calc e₁ = φ.hom ≫ (φ.inv ≫ e₁ ≫ φ.hom) ≫ φ.inv := by
    simp [Iso.hom_inv_id_assoc]
    _ = φ.hom ≫ (φ.inv ≫ e₂ ≫ φ.hom) ≫ φ.inv := by rw [key]
    _ = e₂ := by simp [Iso.hom_inv_id_assoc]

end DegreeTheory

/--
[excision_square_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma excision_square_comm_eq
  {X : Type}
  [TopologicalSpace X]
  {A U : Set X} :
-- imply
  subspaceTopInclusion (Subtype.val ⁻¹' A : Set (Uᶜ : Set X)) ≫ complementInclusion X U = excisedSubsetToSubspace X A U ≫ subspaceTopInclusion A := by
-- proof
  apply Excision.excision_square_comm X A U

/--
[smallChainInclusionA_comp_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma smallChainInclusionA_comp__eq
  {X : Type}
  [TopologicalSpace X]
  {A B : Set X} :
-- imply
  smallChainInclusionA X A B ≫ smallChainInclusion X A B = subspaceChainInclusion X A := by
-- proof
  apply Excision.smallChainInclusionA_comp_ X A B

/--
[sigmaConst_map_mono_of_injective](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma sigmaConst_map_mono_of_injective_eq
  {J K : Type}
  {f : J → K}
  {R : AddCommGrpCat}
-- given
  (hf : Function.Injective f) :
-- imply
  Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
-- proof
  apply Excision.sigmaConst_map_mono_of_injective J K f hf R

/--
[bottomSES_shortExact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma bottomSES_shortExact_eq
  {X : Type}
  [TopologicalSpace X]
  {A : Set X} :
-- imply
  (bottomSES X A).ShortExact := by
-- proof
  apply Excision.bottomSES_shortExact X A

/--
[secondIso_kernel_pullback_cond](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_kernel_pullback_cond_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  (-(kernel.ι (biprod.desc φ ψ) ≫ biprod.fst (X := 𝒜) (Y := ℬ))) ≫ φ = (kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ)) ≫ ψ := by
-- proof
  apply Excision.secondIso_kernel_pullback_cond

/--
[secondIso_fwd_cond](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_fwd_cond_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  pullback.snd φ ψ ≫ (biprod.inr ≫ factorThruImage (biprod.desc φ ψ) ≫ cokernel.π (biprod.inl ≫ factorThruImage (biprod.desc φ ψ))) = 0 := by
-- proof
  apply Excision.secondIso_fwd_cond

/--
[secondIso_kernel_kills_snd_cokernel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_kernel_kills_snd_cokernel_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  kernel.ι (biprod.desc φ ψ) ≫ biprod.snd (X := 𝒜) (Y := ℬ) ≫ cokernel.π (pullback.snd (f := φ) (g := ψ)) = 0 := by
-- proof
  apply Excision.secondIso_kernel_kills_snd_cokernel

/--
[secondIso_inv_kills_inclA](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_inv_kills_inclA_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  (biprod.inl ≫ factorThruImage (biprod.desc φ ψ)) ≫ secondIso_imgToCokerPS φ ψ = 0 := by
-- proof
  apply Excision.secondIso_inv_kills_inclA

/--
[secondIso_fwd_inv_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_fwd_inv_id_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  secondIso_fwd φ ψ ≫ secondIso_inv φ ψ = 𝟙 _ := by
-- proof
  apply Excision.secondIso_fwd_inv_id

/--
[secondIso_inv_fwd_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma secondIso_inv_fwd_id_eq
  [Category 𝒞]
  [Abelian 𝒞] :
-- imply
  secondIso_inv φ ψ ≫ secondIso_fwd φ ψ = 𝟙 _ := by
-- proof
  apply Excision.secondIso_inv_fwd_id

/--
[sigmaConst_map_mono_of_injective'](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma sigmaConst_map_mono_of_injective'_eq
  {J K : Type}
  {f : J → K}
  {R : AddCommGrpCat}
-- given
  (hf : Function.Injective f) :
-- imply
  Mono ((sigmaConst.obj R).map (show J ⟶ K from f)) := by
-- proof
  apply SphereHomology.sigmaConst_map_mono_of_injective' J K f hf R

/--
[addCommGrpCat_endZ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma addCommGrpCat_endZ_apply_eq
  {f : AddCommGrpCat.of ℤ ⟶ AddCommGrpCat.of ℤ}
  {x : ℤ} :
-- imply
  f x = f 1 * x := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.addCommGrpCat_endZ_apply f x

/--
[degreeOfEndo_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma degreeOfEndo_comp_eq
  {G : AddCommGrpCat}
  {φ : G ≅ AddCommGrpCat.of ℤ}
  {e₁ e₂ : G ⟶ G} :
-- imply
  degreeOfEndo φ (e₁ ≫ e₂) = degreeOfEndo φ e₁ * degreeOfEndo φ e₂ := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.degreeOfEndo_comp φ e₁ e₂

/--
[degreeOfEndo_id](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma degreeOfEndo_id_eq
  {G : AddCommGrpCat}
  {φ : G ≅ AddCommGrpCat.of ℤ} :
-- imply
  degreeOfEndo φ (𝟙 G) = 1 := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.degreeOfEndo_id φ

/--
[suspRaw_norm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma suspRaw_norm_eq
  {n : ℕ}
  {f : sphereTopCat n ⟶ sphereTopCat n}
  {v : EuclideanSpace ℝ (Fin (n + 2))}
-- given
  (hv : ‖v‖ = 1) :
-- imply
  ‖suspRaw n f v‖ = 1 := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.suspRaw_norm n f v hv

/--
[suspSafeNorm_val_of_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma suspSafeNorm_val_of_ne_zero_eq
  {n : ℕ}
  {w : EuclideanSpace ℝ (Fin (n + 1))}
-- given
  (hw : w ≠ 0) :
-- imply
  (suspSafeNorm n w).val = ‖w‖⁻¹ • w := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.suspSafeNorm_val_of_ne_zero n w hw

/--
[continuous_suspRaw](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma continuous_suspRaw_eq
  {n : ℕ}
  {f : sphereTopCat n ⟶ sphereTopCat n} :
-- imply
  Continuous (suspRaw n f) := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.continuous_suspRaw n f

/--
[update_neg_mem_sphere](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma update_neg_mem_sphere_eq
  {n : ℕ}
  {i : Fin (n + 1)}
  {x : SphereHomology.Sphere n} :
-- imply
  (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ x.1) i (-(x.1 i))) ∈ Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.update_neg_mem_sphere n i x

/--
[continuous_update_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section10.lean)
-/
@[path]
private lemma continuous_update_neg_eq
  {n : ℕ}
  {i : Fin (n + 1)} :
-- imply
  Continuous (fun v : EuclideanSpace ℝ (Fin (n + 1)) => (WithLp.equiv 2 _).symm (Function.update (WithLp.equiv 2 _ v) i (-(v i)))) := by
-- proof
  apply BrouwerFixedPoint.DegreeTheory.continuous_update_neg n i


-- created on 2026-10-23
