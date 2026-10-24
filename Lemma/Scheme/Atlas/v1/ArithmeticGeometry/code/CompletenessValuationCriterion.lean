import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.ArithmeticGeometry.code.CompletenessValuationCriterion
open AlgebraicGeometry AlgebraicGeometry.CompletenessValuationCriterion


namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[noetherian_finite_union_irreducible](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean)
-/
@[path]
lemma noetherian_finite_union_irreducible
  {k : Type u}
  [Field k]
  {X : AlgVariety k}
  {Y : Type u}
  [TopologicalSpace Y]
  [TopologicalSpace.NoetherianSpace Y]
  {V : Set (X.carrier × Y)}
-- given
  (hV : IsClosed V) :
-- imply
  ∃ (n : ℕ) (components : Fin n → Set (X.carrier × Y)), (∀ i, IsClosed (components i)) ∧ (∀ i, IsIrreducible (components i)) ∧ V = ⋃ i, components i := by
-- proof
  haveI := X.noethProduct Y
  obtain ⟨S, hSfin, hSclosed, hSirr, hSunion⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hV
  lift S to Finset (Set (X.carrier × Y)) using hSfin
  let e := S.equivFin
  refine ⟨S.card, fun i => (e.symm i).val, fun i => ?_, fun i => ?_, ?_⟩
  · exact hSclosed _ (Finset.coe_mem (e.symm i))
  · exact hSirr _ (Finset.coe_mem (e.symm i))
  · rw [hSunion]
    ext x
    simp only [Set.mem_sUnion, Set.mem_iUnion, Finset.mem_coe]
    constructor
    · rintro ⟨t, ht, hx⟩
      exact ⟨e ⟨t, ht⟩, by simpa [e.symm_apply_apply] using hx⟩
    · rintro ⟨i, hx⟩
      exact ⟨(e.symm i).val, Finset.coe_mem (e.symm i), hx⟩

end AlgebraicGeometry.CompletenessValuationCriterion

namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[isClosed_image_finite_union](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean)
-/
@[path]
lemma isClosed_image_finite_union
  {X Y : Type u}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {f : X → Y}
  {n : ℕ}
  {components : Fin n → Set X}
-- given
  (hclosed : ∀ i, IsClosed (f '' (components i))) :
-- imply
  IsClosed (f '' (⋃ i, components i)) := by
-- proof
  rw [Set.image_iUnion]
  exact isClosed_iUnion_of_finite fun i => hclosed i

end AlgebraicGeometry.CompletenessValuationCriterion

namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[valuation_ring_pullback](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean)
-/
@[path]
lemma valuation_ring_pullback
  [Field F₁]
  [Field F₂]
  {ψ : F₁ →+* F₂}
  {S : ValuationSubring F₂}
-- given
  (_hψ : Function.Injective ψ) :
-- imply
  ∃ R : ValuationSubring F₁, ∀ x : F₁, x ∈ R ↔ ψ x ∈ S :=
-- proof
⟨S.comap ψ, fun x => ValuationSubring.mem_comap⟩

end AlgebraicGeometry.CompletenessValuationCriterion

namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[coordring_contained_in_valring](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean)
-/
@[path]
lemma coordring_contained_in_valring
  {k : Type u}
  [Field k]
  [IsAlgClosed k]
  {X : AlgVariety k}
  {Y : Type u}
  [TopologicalSpace Y]
  {V : Set (X.carrier × Y)}
  {dpd : DominantProjectionData X Y V}
  {coordRingY : Subring dpd.Vvar.functionField}
  {S : ValuationSubring dpd.Vvar.functionField}
  {_P₀ : dpd.Z.toVariety.carrier}
-- given
  (hAS : (coordRingY : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField))
  (_hP₀ : ∀ x : dpd.Z.toVariety.functionField, x ∈ dpd.Z.toVariety.localRingAt _P₀ → dpd.psiStar x ∈ S) :
-- imply
  ∃ (coordRingV : Subring dpd.Vvar.functionField), (coordRingY : Set dpd.Vvar.functionField) ⊆ (coordRingV : Set dpd.Vvar.functionField) ∧ (coordRingV : Set dpd.Vvar.functionField) ⊆ (S : Set dpd.Vvar.functionField) :=
-- proof
  ⟨coordRingY, Set.Subset.refl _, hAS⟩

end AlgebraicGeometry.CompletenessValuationCriterion

namespace AlgebraicGeometry.CompletenessValuationCriterion

/--
[isClosed_snd_image_of_closure_subset](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/CompletenessValuationCriterion.lean)
-/
@[path]
lemma isClosed_snd_image_of_closure_subset
  {X Y : Type u}
  [TopologicalSpace X]
  [TopologicalSpace Y]
  {V : Set (X × Y)}
-- given
  (h : closure (Prod.snd '' V) ⊆ Prod.snd '' V) :
-- imply
  IsClosed (Prod.snd '' V) :=
-- proof
  closure_eq_iff_isClosed.mp (Set.Subset.antisymm h subset_closure)

end AlgebraicGeometry.CompletenessValuationCriterion


-- created on 2026-10-23
