import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.NumberTheoryI.code.Prop255
open Filter Set Topology RestrictedProduct
open scoped RestrictedProduct


namespace RestrictedProduct

/--
[mem_XS_of_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma mem_XS_of_restricted
  [DecidableEq ι]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  {x : Πʳ i, [X i, U i]} :
-- imply
  ∃ S : Finset ι, (x : (i : ι) → X i) ∈ XS X U S := by
-- proof
  have hfin := eventually_cofinite.mp x.2
  exact ⟨hfin.toFinset, fun i hi => by
    simp only [Finite.mem_toFinset, mem_setOf_eq, not_not] at hi; exact hi⟩

end RestrictedProduct

namespace RestrictedProduct

/--
[supportFinset_le](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma supportFinset_le
  [DecidableEq ι]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  {T : Finset ι}
  {x : Πʳ i, [X i, U i]}
-- given
  (hx : (x : (i : ι) → X i) ∈ XS X U T) :
-- imply
  supportFinset X U x ⊆ T := by
-- proof
  intro i hi
  simp only [supportFinset, Finite.mem_toFinset, mem_setOf_eq] at hi
  by_contra hiT
  exact hi (hx i hiT)
section DirectLimitConstruction
variable (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

end RestrictedProduct

namespace RestrictedProduct

/--
[cofinite_le_principal_compl](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma cofinite_le_principal_compl
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {S : Finset ι} :
-- imply
  cofinite ≤ principal ((↑S : Set ι)ᶜ) := by
-- proof
  rwa [le_principal_iff, mem_cofinite, compl_compl]
section Homeomorphism
variable (X : ι → Type*) [∀ i, TopologicalSpace (X i)]
  (U : (i : ι) → Set (X i))

end RestrictedProduct

namespace RestrictedProduct

/--
[toDirectLimit_fromDirectLimit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma toDirectLimit_fromDirectLimit
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {q : DirectLimitXS X U} :
-- imply
  toDirectLimit X U (fromDirectLimit X U q) = q := by
-- proof
  obtain ⟨⟨S, x⟩, rfl⟩ := @Quotient.exists_rep _ (directLimitSetoid _ _) q
  show toDirectLimit X U (fromDirectLimit X U (of _ _ S x)) = of _ _ S x
  have key : fromDirectLimit X U (of _ _ S x) = ⟨x.val, XS_mem_restricted X U x.prop⟩ := rfl
  rw [key]
  unfold toDirectLimit
  have h_le : supportFinset X U ⟨x.val, XS_mem_restricted X U x.prop⟩ ≤ S :=
    supportFinset_le X U x.prop
  exact (of_comp (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) h_le _).symm

end RestrictedProduct

namespace RestrictedProduct

/--
[continuous_toChunk](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma continuous_toChunk
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {S : Finset ι} :
-- imply
  Continuous (toChunk X U S) := by
-- proof
  rw [RestrictedProduct.topologicalSpace_eq_of_principal]
  exact continuous_induced_rng.mpr continuous_subtype_val

end RestrictedProduct

namespace RestrictedProduct

/--
[continuous_fromDirectLimit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma continuous_fromDirectLimit
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] :
-- imply
  Continuous (fromDirectLimit X U) := by
-- proof
  apply lift_continuous
  intro S
  have h_filter : Filter.cofinite ≤ Filter.principal ((↑S : Set ι)ᶜ) :=
    cofinite_le_principal_compl S
  rw [show (fun x : ↥(XS X U S) => (⟨(x : (i : ι) → X i), XS_mem_restricted X U x.prop⟩ : Πʳ i, [X i, U i])) =
    RestrictedProduct.inclusion X U h_filter ∘ toChunk X U S from by
    ext x i; rfl]
  exact (RestrictedProduct.continuous_inclusion h_filter).comp (continuous_toChunk X U S)

end RestrictedProduct

namespace RestrictedProduct

/--
[inclusion_mem_XS_of_principal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma inclusion_mem_XS_of_principal
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)]
  {S : Set ι}
  {y : Πʳ i, [X i, U i]_[Filter.principal S]}
-- given
  (hS : Filter.cofinite ≤ Filter.principal S) :
-- imply
  (RestrictedProduct.inclusion X U hS y : (i : ι) → X i) ∈ XS X U (Set.Finite.toFinset (Filter.eventually_cofinite.mp (hS (Filter.mem_principal.mpr (Set.Subset.refl S))))) := by
-- proof
  intro i hi
  have hy := y.2
  rw [Filter.eventually_principal] at hy
  apply hy
  by_contra h
  exact hi ((Set.Finite.mem_toFinset _).mpr h)

end RestrictedProduct

namespace RestrictedProduct

/--
[continuous_toDirectLimit](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
lemma continuous_toDirectLimit
  [DecidableEq ι]
  {X : ι → Type*}
  [∀ i, TopologicalSpace (X i)] :
-- imply
  Continuous (toDirectLimit X U) := by
-- proof
  rw [RestrictedProduct.continuous_dom]
  intro S hS
  have hSc_fin : Set.Finite Sᶜ := by
    rw [← Filter.mem_cofinite]
    exact hS (Filter.mem_principal.mpr (Set.Subset.refl S))
  set T : Finset ι := hSc_fin.toFinset with hT_def
  have key : ∀ y : Πʳ i, [X i, U i]_[Filter.principal S],
    toDirectLimit X U (RestrictedProduct.inclusion X U hS y) =
      of (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) T
        ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
          inclusion_mem_XS_of_principal X U hS y⟩ := by
    intro y
    unfold toDirectLimit
    have h_le : supportFinset X U (RestrictedProduct.inclusion X U hS y) ≤ T :=
      supportFinset_le X U (inclusion_mem_XS_of_principal X U hS y)
    exact (of_comp (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) h_le _).symm
  have heq : toDirectLimit X U ∘ RestrictedProduct.inclusion X U hS =
    (fun y => of (fun S : Finset ι => ↥(XS X U S)) (transitionMaps X U) T
      ⟨(RestrictedProduct.inclusion X U hS y : (i : ι) → X i),
        inclusion_mem_XS_of_principal X U hS y⟩) := by
    ext y; exact key y
  rw [heq]
  apply (of_continuous _ _ T).comp
  apply continuous_induced_rng.mpr
  rwa [RestrictedProduct.topologicalSpace_eq_of_principal]
end RestrictedProduct


/--
[XS_mono](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
private lemma XS_mono_eq
  [DecidableEq ι]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  {S T : Finset ι}
-- given
  (hST : S ⊆ T) :
-- imply
  XS X U S ⊆ XS X U T := by
-- proof
  apply RestrictedProduct.XS_mono X U hST

/--
[mem_XS_support](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
private lemma mem_XS_support_eq
  [DecidableEq ι]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  {x : Πʳ i, [X i, U i]} :
-- imply
  (x : (i : ι) → X i) ∈ XS X U (supportFinset X U x) := by
-- proof
  apply RestrictedProduct.mem_XS_support X U x

/--
[XS_mem_restricted](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Prop255.lean)
-/
@[path]
private lemma XS_mem_restricted_eq
  [DecidableEq ι]
  {X : ι → Type*}
  {U : (i : ι) → Set (X i)}
  {S : Finset ι}
  {x : (i : ι) → X i}
-- given
  (hx : x ∈ XS X U S) :
-- imply
  ∀ᶠ i in cofinite, x i ∈ U i := by
-- proof
  apply RestrictedProduct.XS_mem_restricted X U hx


-- created on 2026-10-23
