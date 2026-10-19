import Mathlib.Data.Set.Card
import Lemma.Finset.NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts
open Finset Function Stirling.conditionset


/--
py claimed `|parts n (k+1)| = |A j|`, but after forgetting block order every `A j` equals the
whole `S2` summand of the Stirling recurrence, whose cardinality is `(k+1) · |parts n (k+1)|`.
-/
@[path]
private lemma main
  {n k : ℕ}
  {j : Fin (k + 1)} :
-- imply
  ((fun x : Fin (k + 1) → Finset ℕ => univ.image (update x j (insert n (x j)))) ''
      Stirling.conditionset n (k + 1)).ncard =
    (k + 1) * ((fun x : Fin (k + 1) → Finset ℕ => univ.image x) ''
      Stirling.conditionset n (k + 1)).ncard := by
-- proof
  set S2 : Set (Finset (Finset ℕ)) :=
    {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e}
  set Aj :=
    (fun x : Fin (k + 1) → Finset ℕ => univ.image (update x j (insert n (x j)))) ''
      Stirling.conditionset n (k + 1)
  have hS2card : S2.ncard = (k + 1) * (parts n (k + 1)).ncard := by
    have hrec := NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts n k
    set S1 : Set (Finset (Finset ℕ)) :=
      {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e}
    have hU : parts (n + 1) (k + 1) = S1 ∪ S2 := by
      ext e
      constructor
      ·
        intro h
        if hn : ({n} : Finset ℕ) ∈ e then
          exact Or.inl ⟨h, hn⟩
        else
          exact Or.inr ⟨h, hn⟩
      ·
        rintro (⟨h, _⟩ | ⟨h, _⟩) <;> exact h
    have hfin := FiniteParts (n + 1) (k + 1)
    have hD : Disjoint S1 S2 := Set.disjoint_left.mpr fun e h1 h2 => h2.2 h1.2
    have hS1card : S1.ncard = (parts n k).ncard := by
      rw [show S1 = _ from SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset,
        ← NcardImageConditionset.eq.NcardImageImageConditionset]
    have hsum : (parts (n + 1) (k + 1)).ncard = S1.ncard + S2.ncard := by
      rw [hU, Set.ncard_union_eq hD (hfin.subset fun e h => h.1) (hfin.subset fun e h => h.1)]
    have h1 := hsum
    have h2 := hrec
    have h3 := hS1card
    omega
  have hAj : Aj = S2 := by
    have hU : S2 = ⋃ i : Fin (k + 1),
        (fun x : Fin (k + 1) → Finset ℕ => univ.image (update x i (insert n (x i)))) ''
          Stirling.conditionset n (k + 1) := by
      dsimp only [S2, parts]
      exact SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J (n := n) (k := k)
    refine Set.Subset.antisymm ?_ ?_
    ·
      intro e he
      exact hU.symm ▸ Set.mem_iUnion.mpr ⟨j, he⟩
    ·
      intro e he
      obtain ⟨i, ⟨x, hx, rfl⟩⟩ := Set.mem_iUnion.mp (hU ▸ he)
      let σ := Equiv.swap i j
      let y : Fin (k + 1) → Finset ℕ := x ∘ σ
      have hy : y ∈ Stirling.conditionset n (k + 1) := by
        refine ⟨?_, ?_, fun m => hx.2.2 (σ m)⟩
        ·
          rw [← hx.1]
          ext a
          simp only [mem_biUnion, mem_univ, true_and, y, comp_apply]
          exact ⟨fun ⟨m, hm⟩ => ⟨σ m, hm⟩,
            fun ⟨m, hm⟩ => ⟨σ.symm m, by simpa [σ] using hm⟩⟩
        ·
          simpa [y, Fintype.sum_equiv σ (fun m => (x (σ m)).card) (fun m => (x m).card)
            fun _ => rfl] using hx.2.1
      refine ⟨y, hy, ?_⟩
      ext b
      simp only [mem_image, mem_univ, true_and]
      constructor
      ·
        rintro ⟨m, rfl⟩
        if hmj : m = j then
          subst hmj
          refine ⟨i, ?_⟩
          simp [y, update_self, σ, Equiv.swap_apply_right]
        else
          have hσi : σ m ≠ i := by
            intro h
            if hmi : m = i then
              exact hmj (hmi ▸ (show j = i by simpa [σ, Equiv.swap_apply_left, hmi] using h).symm)
            else
              exact hmi ((Equiv.swap_apply_of_ne_of_ne hmi hmj).symm.trans h)
          refine ⟨σ m, ?_⟩
          rw [update_of_ne hσi, update_of_ne (show m ≠ j from hmj)]
          rfl
      ·
        rintro ⟨m, rfl⟩
        if hmi : m = i then
          subst hmi
          refine ⟨j, ?_⟩
          simp [y, update_self, σ, Equiv.swap_apply_right]
        else
          have hmj : σ.symm m ≠ j := by
            intro h
            apply hmi
            calc
              _ = σ (σ.symm m) := (Equiv.apply_symm_apply σ m).symm
              _ = σ j := congrArg (⇑σ) h
              _ = i := Equiv.swap_apply_right i j
          refine ⟨σ.symm m, ?_⟩
          rw [update_of_ne hmj, update_of_ne hmi]
          simp [y, σ]
  change Aj.ncard = (k + 1) * (parts n (k + 1)).ncard
  rw [hAj, hS2card]


-- created on 2020-10-05
-- updated on 2026-10-10
