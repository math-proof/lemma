import Mathlib
import Lemma.Bool.Atlas.v1.BooleanFunctions.code.Claim32Lec8.booleanAnalysis.totalInfluence_indicator
open BooleanAnalysis Finset Bool


/--
[card_boundary_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
private lemma main
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A))).card = ∑ i : Fin n, (Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ BooleanAnalysis.flip x i ∉ A) ∨ (x ∉ A ∧ BooleanAnalysis.flip x i ∈ A))).card := by
-- proof
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A)))
    (t := Finset.univ) (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have : (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A))).filter
    (fun p => Prod.snd p = i) =
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (x ∈ A ∧ BooleanAnalysis.flip x i ∉ A) ∨ (x ∉ A ∧ BooleanAnalysis.flip x i ∈ A))).map
      ⟨fun x => (x, i), fun a b h => by simpa using congr_arg Prod.fst h⟩ := by
    ext ⟨x, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, _root_.true_and, Finset.mem_map]
    constructor
    ·
      intro ⟨hP, hj⟩
      subst hj
      exact ⟨x, hP, rfl⟩
    ·
      intro ⟨y, hy, hprod⟩
      cases hprod
      exact ⟨hy, rfl⟩
  rw [this, Finset.card_map]


lemma BooleanAnalysis.card_boundary_eq_sum
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ BooleanAnalysis.flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ BooleanAnalysis.flip p.1 p.2 ∈ A))).card = ∑ i : Fin n, (Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ BooleanAnalysis.flip x i ∉ A) ∨ (x ∉ A ∧ BooleanAnalysis.flip x i ∈ A))).card := by
-- proof
  apply main


-- created on 2026-10-23
-- updated on 2026-11-24
