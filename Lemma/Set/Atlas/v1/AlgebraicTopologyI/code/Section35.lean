import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicTopologyI.code.Section35.Part14
open Set CategoryTheory AlgebraicTopology Limits TopologicalSpace Function neighborhoods of `K`. -/ CategoryTheory.Limits SingularCohomology in Classical inclusion $U_j \hookrightarrow U_i$. $V_j V_i$. CechCohomology
open CategoryTheory AlgebraicTopology Limits TopologicalSpace Function
open neighborhoods of `K`. -/
open CechCohomology Function
open TopologicalSpace SingularCohomology CategoryTheory
open inclusion $U_j \hookrightarrow U_i$. -/
open inclusion $V_j \hookrightarrow V_i$. -/
open Function


namespace CechCohomology

/--
[cofinal_neighborhood_left](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma cofinal_neighborhood_left
  [TopologicalSpace X]
  {A B U V : Set X}
-- given
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hABU : A ∪ B ⊆ U)
  (hBV : B ⊆ V)
  (hVU : V ⊆ U) :
-- imply
  ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ∪ Y ⊆ U ∧ Y ⊆ V :=
-- proof
  ⟨U, V, hU, hV, subset_union_left.trans hABU, hBV, (union_eq_left.mpr hVU).le, Subset.rfl⟩

end CechCohomology

namespace CechCohomology

/--
[inter_inter_union_subset_of_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma inter_inter_union_subset_of_disjoint
  [TopologicalSpace X]
  {U S V T : Set X}
-- given
  (hST : Disjoint S T) :
-- imply
  (U ∩ S) ∩ (V ∪ T) ⊆ V := by
-- proof
  intro x hx
  obtain hxV | hxT := hx.2
  · exact hxV
  · exact (Set.disjoint_iff.mp hST ⟨hx.1.2, hxT⟩).elim

end CechCohomology

namespace CechCohomology

/--
[cofinal_neighborhood_right_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma cofinal_neighborhood_right_normal
  [TopologicalSpace X]
  [NormalSpace X]
  {A B : Set X}
  {U V : Set X}
-- given
  (hA : IsClosed A)
  (hB : IsClosed B)
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hAU : A ⊆ U)
  (hABV : A ∩ B ⊆ V) :
-- imply
  ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V := by
-- proof
  have hclosed_BVc : IsClosed (B ∩ Vᶜ) := hB.inter (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)
  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ := normal_separation hA hclosed_BVc hdisj
  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]
  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

end CechCohomology

namespace CechCohomology

/--
[cofinal_neighborhood_right_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma cofinal_neighborhood_right_compact
  [TopologicalSpace X]
  [T2Space X]
  {A B : Set X}
  {U V : Set X}
-- given
  (hA : IsCompact A)
  (hB : IsCompact B)
  (hU : IsOpen U)
  (hV : IsOpen V)
  (hAU : A ⊆ U)
  (hABV : A ∩ B ⊆ V) :
-- imply
  ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V := by
-- proof
  have hcompact_BVc : IsCompact (B ∩ Vᶜ) := hB.inter_right (isClosed_compl_iff.mpr hV)
  have hdisj : Disjoint A (B ∩ Vᶜ) := by
    rw [Set.disjoint_iff]
    intro x ⟨hxA, hxB, hxV⟩
    exact hxV (hABV ⟨hxA, hxB⟩)
  obtain ⟨S, T, hS, hT, hAS, hBVT, hST⟩ :=
    SeparatedNhds.of_isCompact_isCompact hA hcompact_BVc hdisj
  have hBYT : B ⊆ V ∪ T := by rwa [← compl_compl V, ← Set.inter_subset]
  exact ⟨U ∩ S, V ∪ T, hU.inter hS, hV.union hT,
    subset_inter hAU hAS, hBYT, inter_subset_left,
    inter_inter_union_subset_of_disjoint hST⟩

end CechCohomology

namespace CechCohomology

/--
[neighborhood_maps_cofinal_normal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma neighborhood_maps_cofinal_normal
  [TopologicalSpace X]
  [NormalSpace X]
  {A B : Set X}
-- given
  (hA : IsClosed A)
  (hB : IsClosed B) :
-- imply
  (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U → ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ∪ Y ⊆ U ∧ Y ⊆ V) ∧ (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V → ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V) :=
-- proof
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
    fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_normal hA hB hU hV hAU hABV⟩

end CechCohomology

namespace CechCohomology

/--
[neighborhood_maps_cofinal_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma neighborhood_maps_cofinal_compact
  [TopologicalSpace X]
  [T2Space X]
  {A B : Set X}
-- given
  (hA : IsCompact A)
  (hB : IsCompact B) :
-- imply
  (∀ U V : Set X, IsOpen U → IsOpen V → A ∪ B ⊆ U → B ⊆ V → V ⊆ U → ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ∪ Y ⊆ U ∧ Y ⊆ V) ∧ (∀ U V : Set X, IsOpen U → IsOpen V → A ⊆ U → A ∩ B ⊆ V → ∃ W Y : Set X, IsOpen W ∧ IsOpen Y ∧ A ⊆ W ∧ B ⊆ Y ∧ W ⊆ U ∧ W ∩ Y ⊆ V) :=
-- proof
  ⟨fun _ _ hU hV hABU hBV hVU => cofinal_neighborhood_left hU hV hABU hBV hVU,
    fun _ _ hU hV hAU hABV => cofinal_neighborhood_right_compact hA hB hU hV hAU hABV⟩
end CechCohomology
open CategoryTheory AlgebraicTopology Limits TopologicalSpace Function
noncomputable section
namespace CechCohomology

end CechCohomology

namespace CechCohomology

/--
[addCommGroup_directLimit_map_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma addCommGroup_directLimit_map_exact
  [DecidableEq ι]
  [Preorder ι]
  [IsDirectedOrder ι]
  [Nonempty ι]
  {G : ι → Type*}
  [∀ i, AddCommGroup (G i)]
  {f : ∀ i j, i ≤ j → G i →+ G j}
  [DirectedSystem G fun i j h ↦ f i j h]
  {G' : ι → Type*}
  [∀ i, AddCommGroup (G' i)]
  {f' : ∀ i j, i ≤ j → G' i →+ G' j}
  [DirectedSystem G' fun i j h ↦ f' i j h]
  {G'' : ι → Type*}
  [∀ i, AddCommGroup (G'' i)]
  {f'' : ∀ i j, i ≤ j → G'' i →+ G'' j}
  [DirectedSystem G'' fun i j h ↦ f'' i j h]
-- given
  (p : ∀ i, G i →+ G' i)
  (hp : ∀ i j h, (p j).comp (f i j h) = (f' i j h).comp (p i))
  (q : ∀ i, G' i →+ G'' i)
  (hq : ∀ i j h, (q j).comp (f' i j h) = (f'' i j h).comp (q i))
  (exact_at : ∀ i, Function.Exact (p i) (q i)) :
-- imply
  Function.Exact (AddCommGroup.DirectLimit.map p hp) (AddCommGroup.DirectLimit.map q hq) := by
-- proof
  intro y
  constructor
  · intro hy
    induction y using AddCommGroup.DirectLimit.induction_on with
    | ih i yi =>
      rw [AddCommGroup.DirectLimit.map_apply_of] at hy
      obtain ⟨j, hij, hfq⟩ := AddCommGroup.DirectLimit.of.zero_exact i (q i yi) hy
      have hqf : q j (f' i j hij yi) = 0 := by
        have := DFunLike.congr_fun (hq i j hij) yi
        simp only [AddMonoidHom.coe_comp, Function.comp_apply] at this
        rw [this, hfq]
      obtain ⟨xj, hxj⟩ := ((exact_at j) (f' i j hij yi)).mp hqf
      exact ⟨AddCommGroup.DirectLimit.of G f j xj, by
        rw [AddCommGroup.DirectLimit.map_apply_of, hxj,
          AddCommGroup.DirectLimit.of_f]⟩
  · rintro ⟨x, rfl⟩
    induction x using AddCommGroup.DirectLimit.induction_on with
    | ih i xi =>
      simp only [AddCommGroup.DirectLimit.map_apply_of]
      have : q i (p i xi) = 0 := ((exact_at i) (p i xi)).mpr ⟨xi, rfl⟩
      rw [this, map_zero]

end CechCohomology

/--
[relCochainComplexMap_comp_kernel_ι](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
inclusion equals the kernel inclusion followed by the absolute restriction
cochain map. -/
lemma CechCohomology.relCochainComplexMap_comp_kernel_ι
  {X : Type} [TopologicalSpace X] {K L : Set X}
  (i j : CechCohomology.lesIndexType X K L) (h : i ≤ j) :
  CechCohomology.relCochainComplexMap i j h ≫
    CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j)) =
  CategoryTheory.Limits.kernel.ι
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i)) ≫
  SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
    (CechCohomology.opensInclusion h.1) := by
  simp only [CechCohomology.relCochainComplexMap]
  exact CategoryTheory.Limits.kernel.lift_ι _ _ _

/--
[CechCohomology.ptRelToAbs_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptRelToAbs_nat
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i j : CechCohomology.lesIndexType X K L}
-- given
  (h : i ≤ j) :
-- imply
  (CechCohomology.ptRelToAbs X K L p j).comp (CechCohomology.relBond X K L p i j h) = (CechCohomology.absKBond X K L p i j h).comp (CechCohomology.ptRelToAbs X K L p i) := by
-- proof
  ext x
  show (HomologicalComplex.homologyMap
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j))) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p).hom.toAddMonoidHom x)
  have hsq := CechCohomology.relCochainComplexMap_comp_kernel_ι i j h
  have key : HomologicalComplex.homologyMap
    (CechCohomology.relCochainComplexMap i j h) p ≫
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j))) p =
    HomologicalComplex.homologyMap
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion i))) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p := by
    rw [show HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) p ≫
      HomologicalComplex.homologyMap
        (CategoryTheory.Limits.kernel.ι
          (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
            (CechCohomology.relNbhdInclusion j))) p =
      HomologicalComplex.homologyMap
        (CechCohomology.relCochainComplexMap i j h ≫
          CategoryTheory.Limits.kernel.ι
            (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
              (CechCohomology.relNbhdInclusion j))) p
      from (HomologicalComplex.homologyMap_comp _ _ p).symm, hsq]
    exact HomologicalComplex.homologyMap_comp _ _ p
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2

/--
[CechCohomology.ptRestrict_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptRestrict_nat
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i j : CechCohomology.lesIndexType X K L}
-- given
  (h : i ≤ j) :
-- imply
  (CechCohomology.ptRestrict X K L p j).comp (CechCohomology.absKBond X K L p i j h) = (CechCohomology.absLBond X K L p i j h).comp (CechCohomology.ptRestrict X K L p i) := by
-- proof
  ext x
  show (HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p).hom.toAddMonoidHom x)
  have hcomm : CechCohomology.opensInclusion h.2 ≫ CechCohomology.relNbhdInclusion i =
    CechCohomology.relNbhdInclusion j ≫ CechCohomology.opensInclusion h.1 :=
    (CechCohomology.opensInclusion_comm i j h).symm
  have hsq : SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
    (CechCohomology.opensInclusion h.1) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion j) =
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i) ≫
    SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.2) := by
    rw [← CechCohomology.restrictionCochainMap_comp,
      ← CechCohomology.restrictionCochainMap_comp, hcomm]
  have key : HomologicalComplex.homologyMap
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.opensInclusion h.1)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j)) p =
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)) p ≫
    HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hsq]
  have h2 := congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at h2
  exact h2

/--
[CechCohomology.ptConnecting_nat](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptConnecting_nat
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i j : CechCohomology.lesIndexType X K L}
-- given
  (h : i ≤ j) :
-- imply
  (CechCohomology.ptConnecting X K L p j).comp (CechCohomology.absLBond X K L p i j h) = (CechCohomology.relBond X K L (p + 1) i j h).comp (CechCohomology.ptConnecting X K L p i) := by
-- proof
  let φ : (CategoryTheory.ShortComplex.mk
    (CategoryTheory.Limits.kernel.ι
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion i)))
    (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
      (CechCohomology.relNbhdInclusion i))
    (CategoryTheory.Limits.kernel.condition _)) ⟶
    (CategoryTheory.ShortComplex.mk
      (CategoryTheory.Limits.kernel.ι
        (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
          (CechCohomology.relNbhdInclusion j)))
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.relNbhdInclusion j))
      (CategoryTheory.Limits.kernel.condition _)) :=
    { τ₁ := CechCohomology.relCochainComplexMap i j h
      τ₂ := SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.1)
      τ₃ := SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)
      comm₁₂ := CechCohomology.relCochainComplexMap_comp_kernel_ι i j h
      comm₂₃ := (CechCohomology.restrictionCochainMap_square i j h).symm }
  have key := HomologicalComplex.HomologySequence.δ_naturality φ
    (CechCohomology.cochainSES i) (CechCohomology.cochainSES j) p (p + 1) rfl
  ext x
  show ((CechCohomology.cochainSES j).δ p (p + 1) rfl).hom.toAddMonoidHom
    ((HomologicalComplex.homologyMap
      (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ)
        (CechCohomology.opensInclusion h.2)) p).hom.toAddMonoidHom x) =
    (HomologicalComplex.homologyMap
      (CechCohomology.relCochainComplexMap i j h) (p + 1)).hom.toAddMonoidHom
    (((CechCohomology.cochainSES i).δ p (p + 1) rfl).hom.toAddMonoidHom x)
  have h2 : (HomologicalComplex.homologyMap φ.τ₃ p ≫
    (CechCohomology.cochainSES j).δ p (p + 1) rfl).hom.toAddMonoidHom x =
    ((CechCohomology.cochainSES i).δ p (p + 1) rfl ≫
    HomologicalComplex.homologyMap φ.τ₁ (p + 1)).hom.toAddMonoidHom x :=
    congr_arg (fun f => (ModuleCat.Hom.hom f).toAddMonoidHom x) key.symm
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, LinearMap.comp_apply,
    Function.comp_apply, LinearMap.toAddMonoidHom_coe] at h2 ⊢
  exact h2

/--
[CechCohomology.ptExact_relToAbs_restrict](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptExact_relToAbs_restrict
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i : CechCohomology.lesIndexType X K L} :
-- imply
  Function.Exact (CechCohomology.ptRelToAbs X K L p i) (CechCohomology.ptRestrict X K L p i) := by
-- proof
  have h := (CechCohomology.cochainSES i).homology_exact₂ p
  rwa [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h

/--
[CechCohomology.ptExact_restrict_connecting](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptExact_restrict_connecting
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i : CechCohomology.lesIndexType X K L} :
-- imply
  Function.Exact (CechCohomology.ptRestrict X K L p i) (CechCohomology.ptConnecting X K L p i) := by
-- proof
  have h := (CechCohomology.cochainSES i).homology_exact₃ p (p + 1) rfl
  rwa [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h

/--
[CechCohomology.ptExact_connecting_relToAbs](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
lemma CechCohomology.ptExact_connecting_relToAbs
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {p : ℕ}
  {i : CechCohomology.lesIndexType X K L} :
-- imply
  Function.Exact (CechCohomology.ptConnecting X K L p i) (CechCohomology.ptRelToAbs X K L (p + 1) i) := by
-- proof
  have h := (CechCohomology.cochainSES i).homology_exact₁ p (p + 1) rfl
  rwa [CategoryTheory.ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at h

/--
[opensInclusion_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
private lemma opensInclusion_comm_eq
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {pair₁ pair₂ : RelNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  opensInclusion h.2 ≫ relNbhdInclusion pair₁ = relNbhdInclusion pair₂ ≫ opensInclusion h.1 := by
-- proof
  apply CechCohomology.opensInclusion_comm pair₁ pair₂ h

/--
[restrictionCochainMap_comp](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
private lemma restrictionCochainMap_comp_eq
  {X : Type}
  [TopologicalSpace X]
  {R : Type}
  [CommRing R]
  {G : ModuleCat.{0} R}
  {X Y Z : TopCat.{0}}
  {f : X ⟶ Y}
  {g : Y ⟶ Z} :
-- imply
  restrictionCochainMap R G (f ≫ g) = restrictionCochainMap R G g ≫ restrictionCochainMap R G f := by
-- proof
  apply CechCohomology.restrictionCochainMap_comp R G f g

/--
[restrictionCochainMap_square](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
private lemma restrictionCochainMap_square_eq
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {pair₁ pair₂ : RelNbhdPair K L}
-- given
  (h : pair₁ ≤ pair₂) :
-- imply
  restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₁) ≫ restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.2) = restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (opensInclusion h.1) ≫ restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (relNbhdInclusion pair₂) := by
-- proof
  apply CechCohomology.restrictionCochainMap_square pair₁ pair₂ h

/--
[CechCohomology.relCochainComplexMap_comp_kernel_](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section35.lean)
-/
@[path]
private lemma relCochainComplexMap_comp_kernel__eq
  {X : Type}
  [TopologicalSpace X]
  {K L : Set X}
  {i j : CechCohomology.lesIndexType X K L}
-- given
  (h : i ≤ j) :
-- imply
  CechCohomology.relCochainComplexMap i j h ≫ CategoryTheory.Limits.kernel.ι (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (CechCohomology.relNbhdInclusion j)) = CategoryTheory.Limits.kernel.ι (SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (CechCohomology.relNbhdInclusion i)) ≫ SingularCohomology.restrictionCochainMap ℤ (ModuleCat.of ℤ ℤ) (CechCohomology.opensInclusion h.1) := by
-- proof
  apply CechCohomology.relCochainComplexMap_comp_kernel_ i j h


-- created on 2026-10-23
