import Def.Analysis.MeasureTheory.Section_1_4_2.Part8
import Def.Analysis.MeasureTheory.Section_1_4_3.Part2


/-- Boolean algebras are closed under intersection. -/
lemma ConcreteBooleanAlgebra.inter_mem {X:Type*} (B: ConcreteBooleanAlgebra X) {E F : Set X}
    (hE : B.measurable E) (hF : B.measurable F) : B.measurable (E ∩ F) := by
  rw [Set.inter_eq_compl_compl_union_compl]
  exact B.compl_mem _ (B.union_mem _ _ (B.compl_mem E hE) (B.compl_mem F hF))

/-- Boolean algebras are closed under set difference. -/
lemma ConcreteBooleanAlgebra.diff_mem {X:Type*} (B: ConcreteBooleanAlgebra X) {E F : Set X}
    (hE : B.measurable E) (hF : B.measurable F) : B.measurable (E \ F) := by
  rw [Set.diff_eq]
  exact B.inter_mem hE (B.compl_mem F hF)

/-- Boolean algebras are closed under finite unions. -/
lemma ConcreteBooleanAlgebra.finite_biUnion_mem {X J:Type*} (B: ConcreteBooleanAlgebra X)
    {I: Finset J} {E: J → Set X} (hE: ∀ j, B.measurable (E j)) :
    B.measurable (⋃ j ∈ I, E j) := by
  classical
  refine Finset.induction_on I ?empty ?step
  · simpa using B.empty_mem
  · intro a s ha hs
    rw [Finset.set_biUnion_insert]
    exact B.union_mem _ _ (hE a) hs

/-- Exercise 1.4.20(i) -/
theorem FinitelyAdditiveMeasure.mono {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X} (hE : B.measurable E) (hF : B.measurable F) (hsub : E ⊆ F) : μ.measure E ≤ μ.measure F := by
  have hdiff := B.diff_mem hF hE
  have hdisj : Disjoint E (F \ E) := Set.disjoint_left.mpr fun _ hxE hxd => hxd.2 hxE
  have hunion : E ∪ (F \ E) = F := Set.union_diff_cancel hsub
  have hsum := μ.measure_finite_additive E (F \ E) hE hdiff hdisj
  rw [← hunion, hsum]
  exact le_add_of_nonneg_right (μ.measure_pos (F \ E) hdiff)

/-- Exercise 1.4.20(ii) -/
theorem FinitelyAdditiveMeasure.finite_additivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) (hdisj: Set.univ.PairwiseDisjoint E) :
  μ.measure (⋃ j ∈ I, E j) = ∑ j ∈ I, μ.measure (E j) := by
  classical
  refine Finset.induction_on I ?empty ?step
  · simp [μ.measure_empty]
  · intro a s ha ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    have hunion : B.measurable (⋃ j ∈ s, E j) := B.finite_biUnion_mem hE
    have hdisj' : Disjoint (E a) (⋃ j ∈ s, E j) := by
      rw [Set.disjoint_iUnion₂_right]
      intro j hj
      exact hdisj (Set.mem_univ a) (Set.mem_univ j) (ne_of_mem_of_not_mem hj ha).symm
    rw [μ.measure_finite_additive (E a) (⋃ j ∈ s, E j) (hE a) hunion hdisj', ih]

/-- Exercise 1.4.20(iii) -/
theorem FinitelyAdditiveMeasure.finite_subadditivity {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {J:Type*} {I: Finset J} {E: J → Set X} (hE: ∀ j:J, B.measurable (E j)) :
  μ.measure (⋃ j ∈ I, E j) ≤ ∑ j ∈ I, μ.measure (E j) := by
  classical
  have htwo : ∀ {A C : Set X}, B.measurable A → B.measurable C →
      μ.measure (A ∪ C) ≤ μ.measure A + μ.measure C := by
    intro A C hA hC
    have hdiff := B.diff_mem hC hA
    have hdisj : Disjoint A (C \ A) := Set.disjoint_left.mpr fun _ hxA hxd => hxd.2 hxA
    have hunion : A ∪ (C \ A) = A ∪ C := Set.union_diff_self
    have hsum := μ.measure_finite_additive A (C \ A) hA hdiff hdisj
    rw [← hunion, hsum]
    exact add_le_add (le_refl _) (μ.mono hdiff hC Set.diff_subset)
  refine Finset.induction_on I ?empty ?step
  · simp [μ.measure_empty]
  · intro a s ha ih
    rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
    exact (htwo (hE a) (B.finite_biUnion_mem hE)).trans (add_le_add (le_refl _) ih)

/-- Exercise 1.4.20(iv) -/
theorem FinitelyAdditiveMeasure.mes_union_add_mes_inter {X:Type*} {B: ConcreteBooleanAlgebra X} (μ: FinitelyAdditiveMeasure B) {E F : Set X}
    (hE: B.measurable E) (hF: B.measurable F) :
  μ.measure (E ∪ F) + μ.measure (E ∩ F) = μ.measure E + μ.measure F := by
  have hinter := B.inter_mem hE hF
  have hdiff := B.diff_mem hF hE
  have hdisj₁ : Disjoint E (F \ E) := Set.disjoint_left.mpr fun _ hxE hxd => hxd.2 hxE
  have hdisj₂ : Disjoint (E ∩ F) (F \ E) :=
    Set.disjoint_left.mpr fun _ hx hxd => hxd.2 hx.1
  have h₁ : E ∪ (F \ E) = E ∪ F := Set.union_diff_self
  have h₂ : (E ∩ F) ∪ (F \ E) = F := by
    ext x
    simp [Set.mem_union, Set.mem_inter_iff, Set.mem_diff]
    tauto
  have hsum₁ := μ.measure_finite_additive E (F \ E) hE hdiff hdisj₁
  have hsum₂ := μ.measure_finite_additive (E ∩ F) (F \ E) hinter hdiff hdisj₂
  rw [← h₁, hsum₁, add_assoc, add_comm (μ.measure (F \ E)), ← hsum₂, h₂]

