import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.Claim32Lec8
open BooleanAnalysis
open Finset


namespace BooleanAnalysis

/--
[indicator_ne_iff](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
lemma indicator_ne_iff
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
  {x y : Fin n → Bool} :
-- imply
  indicator A x ≠ indicator A y ↔ (x ∈ A ∧ y ∉ A) ∨ (x ∉ A ∧ y ∈ A) := by
-- proof
  unfold indicator
  constructor
  · intro h
    by_cases hx : x ∈ A <;> by_cases hy : y ∈ A <;> simp_all
  · intro h
    obtain ⟨hx, hny⟩ | ⟨hnx, hy⟩ <;> simp_all := h

end BooleanAnalysis

namespace BooleanAnalysis

/--
[flipCoord_eq_flip](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
lemma flipCoord_eq_flip
  {n : ℕ}
  {x : Fin n → Bool}
  {i : Fin n} :
-- imply
  BooleanFourier.flipCoord x i = flip x i := by
-- proof
  ext j
  by_cases h : j = i
  · subst h; simp [BooleanFourier.flipCoord, flip]
  · simp [BooleanFourier.flipCoord, flip, Function.update_of_ne h]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[totalInfluence_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
lemma totalInfluence_indicator
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  BooleanFourier.totalInfluence (indicator A) = (∑ i : Fin n, ((Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).card : ℝ)) / (2 ^ n : ℝ) := by
-- proof
  unfold BooleanFourier.totalInfluence BooleanFourier.influence
  simp_rw [flipCoord_eq_flip, indicator_ne_iff]
  rw [← Finset.sum_div]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[card_boundary_eq_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
lemma card_boundary_eq_sum
  {n : ℕ}
  {A : Finset (Fin n → Bool)} :
-- imply
  (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n => (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).card = ∑ i : Fin n, (Finset.univ.filter (fun x : Fin n → Bool => (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).card := by
-- proof
  classical
  have h := Finset.card_eq_sum_card_fiberwise (s := Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A)))
    (t := Finset.univ) (f := Prod.snd) (fun _ _ => Finset.mem_univ _)
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  have : (Finset.univ.filter (fun p : (Fin n → Bool) × Fin n =>
    (p.1 ∈ A ∧ flip p.1 p.2 ∉ A) ∨ (p.1 ∉ A ∧ flip p.1 p.2 ∈ A))).filter
    (fun p => Prod.snd p = i) =
    (Finset.univ.filter (fun x : Fin n → Bool =>
      (x ∈ A ∧ flip x i ∉ A) ∨ (x ∉ A ∧ flip x i ∈ A))).map
      ⟨fun x => (x, i), fun a b h => by simpa using congr_arg Prod.fst h⟩ := by
    ext ⟨x, j⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    constructor
    · intro ⟨hP, hj⟩
      subst hj
      exact ⟨x, hP, rfl⟩
    · intro ⟨y, hy, hprod⟩
      cases hprod
      exact ⟨hy, rfl⟩
  rw [this, Finset.card_map]

end BooleanAnalysis

namespace BooleanAnalysis

/--
[edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/Claim32Lec8.lean)
-/
@[path]
lemma edgeBoundaryMeasure_eq_totalInfluence_indicator_div_n
  {n : ℕ}
  {A : Finset (Fin n → Bool)}
-- given
  (hn : n ≠ 0) :
-- imply
  edgeBoundaryMeasure n A = BooleanFourier.totalInfluence (indicator A) / (n : ℝ) := by
-- proof
  rw [edgeBoundaryMeasure_def hn, totalInfluence_indicator, div_div]
  congr 1
  · have hcard := card_boundary_eq_sum A
    exact_mod_cast hcard
  · ring

end BooleanAnalysis


-- created on 2026-10-23
