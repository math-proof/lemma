module

public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.FlatRank
public import Theorem.Scheme.RelEffCartierDivSupportedIn
public import Instance.AlgebraicGeometry_RelEffCartierDivRestrict

public section

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

universe u

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)


@[reassoc (attr := simp)]
public theorem resProdMap_fst : resProdMap f V U hUV gV g hg ≫ pullback.fst f g = pullback.fst _ _ ≫ U.ι := by
  delta resProdMap; exact pullback.lift_fst _ _ _


@[reassoc (attr := simp)]
public theorem resProdMap_snd : resProdMap f V U hUV gV g hg ≫ pullback.snd f g = pullback.snd _ _ := by
  delta resProdMap; exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)


public theorem isPullback_of_comp_mono {A B W Z : Scheme.{u}} (a : A ⟶ W) (b : B ⟶ W) (i : W ⟶ Z) [Mono i]
    {a' : A ⟶ Z} {b' : B ⟶ Z} (ha : a ≫ i = a') (hb : b ≫ i = b') :
    IsPullback (pullback.fst a b) (pullback.snd a b) a' b' := by
  subst ha hb
  exact IsPullback.of_isLimit (pullbackIsPullbackOfCompMono a b i)


public theorem isPullback_resProdMap :
    IsPullback (resProdMap f V U hUV gV g hg) (pullback.fst (f.resLE V U hUV) gV)
      (pullback.fst f g) U.ι := by

  have outer : IsPullback (pullback.snd (f.resLE V U hUV) gV) (pullback.fst (f.resLE V U hUV) gV)
      g (U.ι ≫ f) := by
    exact (isPullback_of_comp_mono (f.resLE V U hUV) gV V.ι (Scheme.Hom.resLE_comp_ι f hUV) hg).flip
  rw [← resProdMap_snd f V U hUV gV g hg] at outer
  exact IsPullback.of_right outer (resProdMap_fst f V U hUV gV g hg) (IsPullback.of_hasPullback f g).flip

end ResProd

end Scheme.RelEffCartierDiv

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)

section ResProd2

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S) (hg : gV ≫ V.ι = g)


public theorem range_resProdMap :
    Set.range (resProdMap f V U hUV gV g hg) = (pullback.fst f g) ⁻¹' (U : Set 𝒞) := by
  have sq := isPullback_resProdMap f V U hUV gV g hg
  rw [← sq.isoPullback_hom_fst, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
    Set.range_eq_univ.mpr sq.isoPullback.hom.surjective, Set.image_univ, Scheme.Pullback.range_fst,
    Scheme.Opens.range_ι]


public theorem range_resProdMap' :
    Set.range (resProdMap f V U hUV gV g hg) = ((pullback.fst f g) ⁻¹ᵁ U : (pullback f g).Opens) :=
  range_resProdMap f V U hUV gV g hg

end ResProd2

variable {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)

section Restrict

variable (hg : gV ≫ V.ι = g) (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U)

include hD in


public theorem isIso_pullback_snd_resProdMap :
    IsIso (pullback.snd (resProdMap f V U hUV gV g hg) D.I.subschemeι) := by
  apply isIso_of_isOpenImmersion_of_opensRange_eq_top
  ext1
  rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Pullback.range_snd,
    range_resProdMap, Set.eq_univ_iff_forall]
  intro z
  change pullback.fst f g (D.I.subschemeι z) ∈ (U : Set 𝒞)
  have hz : D.I.subschemeι z ∈ (D.I.support : Set ↥(pullback f g)) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
  exact hD hz


@[simp] public theorem restrictAlong_I :
    (restrictAlong f r V U hUV gV g hg D hD).I = D.I.comap (resProdMap f V U hUV gV g hg) := rfl

end Restrict

section Extend

variable (hg : gV ≫ V.ι = g) (D' : RelEffCartierDiv (f.resLE V U hUV) r gV)

variable [IsSeparated f]


@[simp] public theorem extendAlong_I :
    (extendAlong f r V U hUV gV g hg D').I = (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg).ker := rfl


public theorem extendAlong_I_eq_map :
    (extendAlong f r V U hUV gV g hg D').I = D'.I.map (resProdMap f V U hUV gV g hg) := rfl


public theorem extendAlong_supportedIn : (extendAlong f r V U hUV gV g hg D').SupportedIn U := by
  intro z hz
  rw [extendAlong_I, Scheme.Hom.support_ker, IsClosed.closure_eq
    (D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg).isClosedEmbedding.isClosed_range] at hz
  obtain ⟨w, rfl⟩ := hz
  show pullback.fst f g ((D'.I.subschemeι ≫ resProdMap f V U hUV gV g hg) w) ∈ U
  have : resProdMap f V U hUV gV g hg (D'.I.subschemeι w) ∈ Set.range (resProdMap f V U hUV gV g hg) :=
    Set.mem_range_self _
  rw [range_resProdMap] at this
  exact this

end Extend

end Scheme.RelEffCartierDiv

namespace Scheme.RelEffCartierDiv

variable {𝒞 S : Scheme.{u}} (f : 𝒞 ⟶ S) (r : ℕ) (V : S.Opens) (U : 𝒞.Opens) (hUV : U ≤ f ⁻¹ᵁ V)
  {T : Scheme.{u}} (gV : T ⟶ V) (g : T ⟶ S)

section RoundTrip

variable [IsSeparated f] (hg : gV ≫ V.ι = g)


@[simp] public theorem extendAlong_restrictAlong (D : RelEffCartierDiv f r g) (hD : D.SupportedIn U) :
    extendAlong f r V U hUV gV g hg (restrictAlong f r V U hUV gV g hg D hD) = D := by
  haveI := isIso_pullback_snd_resProdMap f r V U hUV gV g hg D hD
  refine RelEffCartierDiv.ext ?_
  rw [extendAlong_I, restrictAlong_I, ← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc,
    pullback.condition, ← Category.assoc, Scheme.Hom.ker_comp_of_isIso,
    Scheme.IdealSheafData.ker_subschemeι]


@[simp] public theorem restrictAlong_extendAlong (D' : RelEffCartierDiv (f.resLE V U hUV) r gV) :
    restrictAlong f r V U hUV gV g hg (extendAlong f r V U hUV gV g hg D')
      (extendAlong_supportedIn f r V U hUV gV g hg D') = D' := by
  refine RelEffCartierDiv.ext ?_
  set j := resProdMap f V U hUV gV g hg with hj
  set h := D'.I.subschemeι ≫ j with hh
  rw [restrictAlong_I, extendAlong_I, ← hj, ← hh, ← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion h j]

  have hfst : pullback.fst j h = pullback.snd j h ≫ D'.I.subschemeι :=
    (cancel_mono j).mp (by rw [Category.assoc, pullback.condition])
  haveI : IsIso (pullback.snd j h) := by
    apply isIso_of_isOpenImmersion_of_opensRange_eq_top
    ext1
    rw [Scheme.Hom.coe_opensRange, TopologicalSpace.Opens.coe_top, Scheme.Pullback.range_snd,
      Set.eq_univ_iff_forall]
    intro z
    exact ⟨D'.I.subschemeι z, (Scheme.Hom.comp_apply _ _ _).symm⟩
  rw [hfst, Scheme.Hom.ker_comp_of_isIso, Scheme.IdealSheafData.ker_subschemeι]

end RoundTrip

section Naturality


public theorem isPullback_mapOnProdOver_resProdMap {T₁ T₂ : Scheme.{u}} {gV₁ : T₁ ⟶ V} {gV₂ : T₂ ⟶ V}
    {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} (hg₁ : gV₁ ≫ V.ι = g₁) (hg₂ : gV₂ ≫ V.ι = g₂)
    (φ : T₁ ⟶ T₂) (hφV : φ ≫ gV₂ = gV₁) (hφ : φ ≫ g₂ = g₁) :
    IsPullback (mapOnProdOver (f.resLE V U hUV) φ hφV) (resProdMap f V U hUV gV₁ g₁ hg₁)
      (resProdMap f V U hUV gV₂ g₂ hg₂) (mapOnProdOver f φ hφ) := by
  have s := (isPullback_resProdMap f V U hUV gV₁ g₁ hg₁).flip

  rw [← mapOnProdOver_fst (f.resLE V U hUV) φ hφV, ← mapOnProdOver_fst f φ hφ] at s
  refine IsPullback.of_right s ?_ (isPullback_resProdMap f V U hUV gV₂ g₂ hg₂).flip
  apply pullback.hom_ext
  · simp only [Category.assoc, resProdMap_fst, mapOnProdOver_fst, mapOnProdOver_fst_assoc]
  · simp only [Category.assoc, resProdMap_snd, mapOnProdOver_snd, resProdMap_snd_assoc]

variable [IsSeparated f] in


public theorem extendAlong_pullbackAlong {T₁ T₂ : Scheme.{u}} {gV₁ : T₁ ⟶ V} {gV₂ : T₂ ⟶ V}
    {g₁ : T₁ ⟶ S} {g₂ : T₂ ⟶ S} (hg₁ : gV₁ ≫ V.ι = g₁) (hg₂ : gV₂ ≫ V.ι = g₂)
    (D' : RelEffCartierDiv (f.resLE V U hUV) r gV₂) (φ : T₁ ⟶ T₂) (hφV : φ ≫ gV₂ = gV₁)
    (hφ : φ ≫ g₂ = g₁) :
    extendAlong f r V U hUV gV₁ g₁ hg₁ (D'.pullbackAlong φ hφV) =
      (extendAlong f r V U hUV gV₂ g₂ hg₂ D').pullbackAlong φ hφ := by
  refine RelEffCartierDiv.ext ?_
  set j₁ := resProdMap f V U hUV gV₁ g₁ hg₁ with hj₁
  set j₂ := resProdMap f V U hUV gV₂ g₂ hg₂ with hj₂
  set m := mapOnProdOver (f.resLE V U hUV) φ hφV with hm
  set M := mapOnProdOver f φ hφ with hM
  set h₂ := D'.I.subschemeι ≫ j₂ with hh₂
  change ((D'.I.comap m).subschemeι ≫ j₁).ker = (h₂.ker).comap M
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion h₂ M,
    ← Scheme.IdealSheafData.comapIso_hom_fst, Category.assoc, Scheme.Hom.ker_comp_of_isIso]

  have big : IsPullback (pullback.fst m D'.I.subschemeι ≫ j₁) (pullback.snd m D'.I.subschemeι) M h₂ :=
    ((IsPullback.of_hasPullback m D'.I.subschemeι).flip.paste_vert
      (isPullback_mapOnProdOver_resProdMap f V U hUV hg₁ hg₂ φ hφV hφ)).flip
  rw [← big.isoPullback_hom_fst, Scheme.Hom.ker_comp_of_isIso]

end Naturality

section Range

include hUV in


public theorem range_subset_of_supportedIn {g : T ⟶ S} (D : RelEffCartierDiv f r g)
    (hD : D.SupportedIn U) (hr : 0 < r) : Set.range g ⊆ Set.range V.ι := by
  rintro _ ⟨t, rfl⟩
  have := D.isFinite; have := D.flat; have := D.locallyOfFinitePresentation
  have hsurj : Surjective (D.I.subschemeι ≫ pullback.snd f g) := by
    rw [← Scheme.Hom.one_le_finrank_iff_surjective]
    intro t; rw [D.finrank_eq]; exact hr
  obtain ⟨z, hz⟩ := hsurj.surj t
  have hzU : pullback.fst f g (D.I.subschemeι z) ∈ U := by
    have hz' : D.I.subschemeι z ∈ (D.I.support : Set ↥(pullback f g)) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]; exact Set.mem_range_self z
    exact hD hz'
  rw [Scheme.Opens.range_ι]
  change g t ∈ V
  rw [← hz, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply _ g, ← pullback.condition,
    Scheme.Hom.comp_apply]
  exact hUV hzU

end Range

end Scheme.RelEffCartierDiv
