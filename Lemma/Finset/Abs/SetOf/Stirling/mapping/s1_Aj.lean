import sympy.sets.stirling_partition
import sympy.Basic
import Mathlib.Data.Set.Card
import Lemma.Finset.NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts
import Lemma.Finset.NcardImageConditionset.eq.NcardImageImageConditionset
import Lemma.Finset.SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J
import Lemma.Finset.SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset
import Lemma.Finset.FiniteParts
open Finset Stirling.conditionset


/--
py claimed `|parts n (k+1)| = |A j|`, but after forgetting block order every `A j` equals the
whole `S2` summand of the Stirling recurrence, whose cardinality is `(k+1) · |parts n (k+1)|`.
-/
@[path]
private lemma main
  {n k : ℕ}
  {j : Fin (k + 1)} :
-- imply
  ((fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j (insert n (x j)))) ''
      Stirling.conditionset n (k + 1)).ncard =
    (k + 1) * ((fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image x) ''
      Stirling.conditionset n (k + 1)).ncard := by
-- proof
  set A : Fin (k + 1) → Set (Finset (Finset ℕ)) := fun j' =>
    (fun x : Fin (k + 1) → Finset ℕ => Finset.univ.image (Function.update x j' (insert n (x j')))) ''
      Stirling.conditionset n (k + 1)
  set S2 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∉ e}
  have hS2 : S2 = ⋃ i : Fin (k + 1), A i :=
    (SetOfIn_ImageConditionset_Add_1Add_1AndFinset.eq.J (n := n) (k := k)).symm
  have reorder :
      ∀ {i : Fin (k + 1)} {x : Fin (k + 1) → Finset ℕ},
        x ∈ Stirling.conditionset n (k + 1) →
          ∃ y ∈ Stirling.conditionset n (k + 1),
            Finset.univ.image (Function.update y j (insert n (y j))) =
              Finset.univ.image (Function.update x i (insert n (x i))) := by
    intro i x hx
    let σ := Equiv.swap i j
    let y : Fin (k + 1) → Finset ℕ := x ∘ σ
    have hy : y ∈ Stirling.conditionset n (k + 1) := by
      refine ⟨?_, ?_, fun m => hx.2.2 (σ m)⟩
      ·
        rw [← hx.1]
        ext a
        simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, y, Function.comp_apply]
        exact ⟨fun ⟨m, hm⟩ => ⟨σ m, hm⟩, fun ⟨m, hm⟩ => ⟨σ.symm m, by simpa [σ] using hm⟩⟩
      ·
        calc
          ∑ m, (y m).card = ∑ m, (x (σ m)).card := rfl
          _ = ∑ m, (x m).card :=
            Fintype.sum_equiv σ (fun m => (x (σ m)).card) (fun m => (x m).card) fun _ => rfl
          _ = n := hx.2.1
    refine ⟨y, hy, ?_⟩
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and, y, Function.comp_apply]
    constructor
    ·
      rintro ⟨m, rfl⟩
      by_cases hmj : m = j
      ·
        subst hmj
        exact ⟨i, by simp [Function.update_same, σ, Equiv.swap_apply_right]⟩
      ·
        have hσi : σ m ≠ i := fun h => hmj (by
          -- Equiv.swap i j m = i ↔ m = j
          have := (Equiv.swap_apply_eq_iff (a := i) (b := j) (c := m)).1 h
          simpa [Equiv.swap_apply_left] using this)
        exact ⟨σ m, by rw [Function.update_of_ne hmj, Function.update_of_ne hσi]⟩
    ·
      rintro ⟨m, rfl⟩
      by_cases hmi : m = i
      ·
        subst hmi
        exact ⟨j, by simp [Function.update_same, σ, Equiv.swap_apply_right]⟩
      ·
        have hmj : σ.symm m ≠ j := fun h => hmi (by
          simpa [σ, Equiv.swap_apply_right] using (congrArg σ h).symm)
        exact ⟨σ.symm m, by
          rw [Function.update_of_ne hmj, Function.update_of_ne hmi]
          simp [σ]⟩
  have hAj : A j = S2 := by
    refine le_antisymm (fun e he => hS2 ▸ Set.mem_iUnion.mpr ⟨j, he⟩) ?_
    intro e he
    obtain ⟨i, ⟨x, hx, rfl⟩⟩ := Set.mem_iUnion.mp (hS2 ▸ he)
    obtain ⟨y, hy, himg⟩ := reorder (i := i) hx
    exact ⟨y, hy, himg⟩
  have hS2card : S2.ncard = (k + 1) * (parts n (k + 1)).ncard := by
    have hrec := NcardParts_Add_1_Add_1.eq.AddNcardPartsMulAdd_1NcardParts n k
    set S1 := {e | e ∈ parts (n + 1) (k + 1) ∧ ({n} : Finset ℕ) ∈ e}
    have hU : parts (n + 1) (k + 1) = S1 ∪ S2 := by
      ext e
      simp only [Set.mem_union, Set.mem_ofPred_eq]
      tauto
    have hfin := FiniteParts (n + 1) (k + 1)
    have hD : Disjoint S1 S2 := Set.disjoint_left.mpr fun e h1 h2 => h2.2 h1.2
    have hS1card : S1.ncard = (parts n k).ncard := by
      rw [show S1 = _ from SetOfIn_ImageConditionsetAndInFinset.eq.ImageImageConditionset]
      exact NcardImageConditionset.eq.NcardImageImageConditionset.symm
    have hsum : (parts (n + 1) (k + 1)).ncard = S1.ncard + S2.ncard := by
      rw [hU, Set.ncard_union_eq hD (hfin.subset fun e h => h.1) (hfin.subset fun e h => h.1)]
    lia [hsum, hrec, hS1card]
  simpa [A, parts, hAj] using hS2card


-- created on 2026-10-07
