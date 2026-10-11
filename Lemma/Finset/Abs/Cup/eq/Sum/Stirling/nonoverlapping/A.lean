import sympy.functions.combinatorial.numbers
import sympy.Basic
import Mathlib.Data.Set.Card
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Fintype.Pi
import Lemma.Finset.Eq.of.In.In.In_Conditionset
import Lemma.Finset.Subset_Range.of.In_Conditionset
open Finset Function


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
  (_ : k < n) :
-- imply
  let A : Fin (k + 1) → Set (Fin (k + 1) → Finset ℕ) := fun j =>
    (fun x : Fin (k + 1) → Finset ℕ => update x j (insert n (x j))) ''
      Stirling.conditionset n (k + 1)
  (⋃ j, A j).ncard = ∑ j, (A j).ncard := by
-- proof
  let A : Fin (k + 1) → Set (Fin (k + 1) → Finset ℕ) := fun j =>
    (fun x : Fin (k + 1) → Finset ℕ => update x j (insert n (x j))) ''
      Stirling.conditionset n (k + 1)
  have hmem_cs :
    ∀ {j : Fin (k + 1)} {x : Fin (k + 1) → Finset ℕ},
      x ∈ Stirling.conditionset n (k + 1) →
        update x j (insert n (x j)) ∈ Stirling.conditionset (n + 1) (k + 1) := by
    intro j x hx
    refine ⟨?_, ?_, ?_⟩
    ·
      ext a
      simp only [mem_biUnion, mem_univ, true_and, mem_range]
      constructor
      ·
        rintro ⟨i, ha⟩
        if hij : i = j then
          subst hij
          have : a ∈ insert n (x i) := by simpa [update_self] using ha
          obtain rfl | ha' := mem_insert.mp this
          · omega
          · exact Nat.lt_succ_of_lt (mem_range.mp (Subset_Range.of.In_Conditionset hx i ha'))
        else
          exact Nat.lt_succ_of_lt (mem_range.mp (Subset_Range.of.In_Conditionset hx i (by simpa [update_of_ne hij] using ha)))
      ·
        intro ha
        obtain hlt | rfl := Nat.lt_or_eq_of_le (Nat.lt_succ_iff.mp ha)
        ·
          obtain ⟨i, -, hi⟩ := mem_biUnion.mp (hx.1 ▸ mem_range.mpr hlt)
          if hij : i = j then
            subst hij
            exact ⟨i, by simp [update_self, hi]⟩
          else
            exact ⟨i, by simpa [update_of_ne hij] using hi⟩
        · exact ⟨j, by simp [update_self]⟩
    ·
      have hcard :
        ∀ i, (update x j (insert n (x j)) i).card =
          (x i).card + if i = j then 1 else 0 := by
        intro i
        if hij : i = j then
          subst hij
          have hn : n ∉ x i := fun h =>
            (lt_irrefl n) (mem_range.mp (Subset_Range.of.In_Conditionset hx i h))
          simp [update_self, card_insert_of_notMem hn]
        else
          simp [hij]
      calc
        _ = ∑ i, ((x i).card + if i = j then 1 else 0) := by simp [hcard]
        _ = ∑ i, (x i).card + ∑ i : Fin (k + 1), (if i = j then 1 else 0) := by simp [sum_add_distrib]
        _ = n + 1 := by simp [hx.2.1, sum_ite_eq']
    ·
      intro i
      if hij : i = j then
        subst hij
        simp only [update_self]
        exact lt_of_lt_of_le (hx.2.2 i) (card_le_card (subset_insert _ _))
      else
        simpa [update_of_ne hij] using hx.2.2 i
  have hfin_cs : (Stirling.conditionset n (k + 1)).Finite := by
    refine (Set.Finite.pi' fun _ : Fin (k + 1) => (range n).powerset.finite_toSet).subset ?_
    intro x hx i
    exact mem_powerset.mpr (Subset_Range.of.In_Conditionset hx i)
  have hAfin : ∀ j, (A j).Finite := fun j => hfin_cs.image _
  have hdisj : Pairwise fun j₁ j₂ => Disjoint (A j₁) (A j₂) := by
    intro j₁ j₂ hj₁₂
    refine Set.disjoint_left.mpr fun y hy₁ hy₂ => ?_
    obtain ⟨x₁, hx₁, rfl⟩ := hy₁
    obtain ⟨x₂, hx₂, heq⟩ := hy₂
    exact hj₁₂ (Eq.of.In.In.In_Conditionset (hmem_cs hx₁)
      (show n ∈ update x₁ j₁ (insert n (x₁ j₁)) j₁ by simp [update_self])
      (by rw [show update x₁ j₁ (insert n (x₁ j₁)) = update x₂ j₂ (insert n (x₂ j₂)) from heq.symm]; simp [update_self]))
  have h := Set.ncard_iUnion_of_finite (s := A) hAfin (fun {a b} hab => hdisj hab)
  simpa [finsum_eq_sum_of_fintype] using h


-- created on 2020-08-11
-- updated on 2026-10-10
