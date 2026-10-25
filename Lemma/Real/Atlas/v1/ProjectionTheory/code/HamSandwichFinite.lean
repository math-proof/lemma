import Mathlib
import sympy.Basic
import Def.v1.Atlas.ProjectionTheory.code.PolynomialHamSandwich
import Lemma.Real.Atlas.v1.ProjectionTheory.code.PolynomialHamSandwich
open Finset MvPolynomial


namespace HamSandwich

/--
[ham_sandwich_finite](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ProjectionTheory/code/HamSandwichFinite.lean)
-/
@[path]
lemma ham_sandwich_finite
  {n : ℕ}
  {N : ℕ}
  {S : Fin N → Finset (Fin n → ℝ)}
-- given
  (hn : 0 < n) :
-- imply
  ∃ p : MvPolynomial (Fin n) ℝ, p ≠ 0 ∧ ∀ i : Fin N, ((S i).filter (fun x => MvPolynomial.eval x p > 0)).card ≤ (S i).card / 2 ∧ ((S i).filter (fun x => MvPolynomial.eval x p < 0)).card ≤ (S i).card / 2 := by
-- proof
  classical
  let allPts : Finset (Fin n → ℝ) := Finset.univ.biUnion S
  let p := allPts.prod (fun a => X (⟨0, hn⟩ : Fin n) - C (a ⟨0, hn⟩))
  refine ⟨p, ?_, fun i => ?_⟩
  ·
    rw [Finset.prod_ne_zero_iff]
    intro a _ h
    have h1 : (X (⟨0, hn⟩ : Fin n) : MvPolynomial (Fin n) ℝ) = C (a ⟨0, hn⟩) :=
      sub_eq_zero.mp h
    have h2 := MvPolynomial.totalDegree_X (R := ℝ) (⟨0, hn⟩ : Fin n)
    have h3 := MvPolynomial.totalDegree_C (a ⟨0, hn⟩) (σ := Fin n)
    linarith [h1 ▸ h3]
  ·
    have heval : ∀ x ∈ S i, eval x p = 0 := by
      intro x hx
      simp only [p, map_prod, eval_sub, eval_X, eval_C]
      exact Finset.prod_eq_zero
        (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, hx⟩) (by ring)
    constructor
    · have hempty : (S i).filter (fun x => eval x p > 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx; simp only [not_lt]; linarith [heval x hx]
      rw [hempty, Finset.card_empty]; exact Nat.zero_le _
    · have hempty : (S i).filter (fun x => eval x p < 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro x hx; simp only [not_lt]; linarith [heval x hx]
      rw [hempty, Finset.card_empty]; exact Nat.zero_le _

end HamSandwich


-- created on 2026-10-23
