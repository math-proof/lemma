import Mathlib
import Initialize.Tactic.Attr.Basic
open IntermediateField


/--
[function_field_generators](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/FunctionFieldGenerators.lean)
-/
@[path]
lemma function_field_generators
  {k F : Type*}
  [Field k]
  [Field F]
  [Algebra k F]
  [IsAlgClosed k]
  [Algebra.EssFiniteType k F]
  {n : ℕ}
-- given
  (hdim : Algebra.trdeg k F = n) :
-- imply
  ∃ (t : Fin n → F) (α : F), AlgebraicIndependent k t ∧ IsAlgebraic (adjoin k (Set.range t)) α ∧ adjoin k (insert α (Set.range t)) = ⊤ := by
-- proof
  haveI : PerfectField k := IsAlgClosed.perfectField k
  obtain ⟨s, hs_basis, hs_sep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k F
  have h_range : Set.range (Subtype.val : s → F) = (s : Set F) := Subtype.range_coe
  have h_card_eq : Cardinal.mk s = (n : Cardinal) := by
    rw [hs_basis.cardinalMk_eq_trdeg, hdim]
  have h_finset_card : s.card = n := by
    rw [Cardinal.mk_fintype, Fintype.card_coe] at h_card_eq
    exact_mod_cast h_card_eq
  let e := (Finset.equivFinOfCardEq h_finset_card).symm
  let t : Fin n → F := Subtype.val ∘ e
  have ht_indep : AlgebraicIndependent k t := hs_basis.1.comp e e.injective
  have ht_range : Set.range t = (s : Set F) := by
    simp only [t, Set.range_comp, Equiv.range_eq_univ, Set.image_univ]
    exact Subtype.range_coe
  have h_alg : Algebra.IsAlgebraic (adjoin k (Set.range t)) F := by
    rwa [ht_range, ← h_range]
  haveI : Algebra.EssFiniteType (adjoin k (Set.range t)) F := by
    rw [ht_range]; exact Algebra.EssFiniteType.of_comp k _ _
  haveI : FiniteDimensional (adjoin k (Set.range t)) F :=
    Algebra.finite_of_essFiniteType_of_isAlgebraic
  haveI : Algebra.IsSeparable (adjoin k (Set.range t)) F := by
    rw [ht_range]; exact hs_sep
  obtain ⟨α, hα⟩ := Field.exists_primitive_element (adjoin k (Set.range t)) F
  refine ⟨t, α, ht_indep, h_alg.isAlgebraic α, ?_⟩
  have h1 := adjoin_adjoin_left k (Set.range t) {α}
  rw [hα] at h1
  rw [Set.union_comm, Set.singleton_union] at h1
  rw [← h1]
  ext x; simp [restrictScalars]


-- created on 2026-10-23
