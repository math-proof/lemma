import sympy.functions.combinatorial.numbers
import sympy.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Lemma.Finset.Eq.of.In.In.In_Conditionset
import Lemma.Finset.Subset_Range.of.In_Conditionset


/--
py claimed `|⋃ⱼ Aⱼ| = Σⱼ |Aⱼ|` for the *unordered* images `Finset.univ.image (update …)`,
but those `Aⱼ` coincide (not pairwise disjoint). The nonoverlapping count holds for the
*ordered* updates below: each ordered partition of `range (n+1)` with `n` not a singleton
block lies in exactly one `A j`.
-/
@[path]
private lemma main
  {n k : ℕ}
-- given
  (_h : k < n) :
-- imply
  let A : Fin (k + 1) → Set (Fin (k + 1) → Finset ℕ) := fun j =>
    (fun x : Fin (k + 1) → Finset ℕ => Function.update x j (insert n (x j))) ''
      Stirling.conditionset n (k + 1)
  (⋃ j, A j).ncard = ∑ j, (A j).ncard := by
-- proof
  let A : Fin (k + 1) → Set (Fin (k + 1) → Finset ℕ) := fun j =>
    (fun x : Fin (k + 1) → Finset ℕ => Function.update x j (insert n (x j))) ''
      Stirling.conditionset n (k + 1)
  have hmem_cs :
      ∀ {j : Fin (k + 1)} {x : Fin (k + 1) → Finset ℕ},
        x ∈ Stirling.conditionset n (k + 1) →
          Function.update x j (insert n (x j)) ∈ Stirling.conditionset (n + 1) (k + 1) := by
    intro j x hx
    refine ⟨?_, ?_, ?_⟩
    ·
      ext a
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_range]
      constructor
      ·
        rintro ⟨i, ha⟩
        if hij : i = j then
          subst hij
          simp only [Function.update_same, Finset.mem_insert] at ha
          obtain rfl | ha := ha
          · omega
          · have := Finset.mem_range.mp ((Subset_Range.of.In_Conditionset hx i) ha)
            omega
        else
          rw [Function.update_of_ne hij] at ha
          have := Finset.mem_range.mp ((Subset_Range.of.In_Conditionset hx i) ha)
          omega
      ·
        intro ha
        obtain hlt | rfl := Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha)
        ·
          obtain ⟨i, hi⟩ := Finset.mem_biUnion.mp (hx.1 ▸ Finset.mem_range.mpr hlt)
          exact ⟨i, by
            if hij : i = j then
              subst hij
              simp [Function.update_same, Finset.mem_insert, hi]
            else
              rwa [Function.update_of_ne hij]⟩
        · exact ⟨j, by simp [Function.update_same, Finset.mem_insert]⟩
    ·
      have hcard :
          ∀ i, (Function.update x j (insert n (x j)) i).card =
            (x i).card + if i = j then 1 else 0 := by
        intro i
        if hij : i = j then
          subst hij
          simp only [Function.update_same, if_true]
          have hn : n ∉ x j := fun h => by
            have := Finset.mem_range.mp ((Subset_Range.of.In_Conditionset hx j) h)
            exact Nat.lt_irrefl _ this
          rw [Finset.card_insert_of_notMem hn]
        else
          simp [Function.update_of_ne hij, hij]
      calc
        ∑ i, (Function.update x j (insert n (x j)) i).card
            = ∑ i, ((x i).card + if i = j then 1 else 0) := by simp [hcard]
          _ = ∑ i, (x i).card + ∑ i : Fin (k + 1), (if i = j then 1 else 0) := by
              simp [Finset.sum_add_distrib]
          _ = n + 1 := by
              simp [hx.2.1, Finset.sum_ite_eq']
    ·
      intro i
      if hij : i = j then
        subst hij
        simp only [Function.update_same]
        exact lt_of_lt_of_le (hx.2.2 i) (Finset.card_le_card (Finset.subset_insert _ _))
      else
        simpa [Function.update_of_ne hij] using hx.2.2 i
  have hfin_cs : (Stirling.conditionset n (k + 1)).Finite := by
    refine ((Finset.finite_toSet ((Finset.range n).powerset)).finite_pi).subset ?_
    intro x hx i
    exact Finset.mem_powerset.mpr (Subset_Range.of.In_Conditionset hx i)
  have hAfin : ∀ j, (A j).Finite := fun j => hfin_cs.image _
  have hdisj : Pairwise (Disjoint on A) := by
    intro j₁ j₂ hj₁₂
    refine Set.disjoint_left.mpr fun y hy₁ hy₂ => ?_
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, heq⟩ := hy₂
    have hn₁ : n ∈ Function.update x₁ j₁ (insert n (x₁ j₁)) j₁ := by
      simp [Function.update_same, Finset.mem_insert]
    have hn₂ : n ∈ Function.update x₁ j₁ (insert n (x₁ j₁)) j₂ := by
      have : Function.update x₁ j₁ (insert n (x₁ j₁)) = Function.update x₂ j₂ (insert n (x₂ j₂)) :=
        heq.symm
      simp only [this, Function.update_same, Finset.mem_insert, true_or]
    have : j₁ = j₂ :=
      Eq.of.In.In.In_Conditionset (hmem_cs hx₁) hn₁ hn₂
    exact hj₁₂ this
  have h := Set.ncard_iUnion_of_finite (s := A) hAfin hdisj
  simpa [finsum_eq_sum_of_fintype] using h


-- created on 2020-08-11
