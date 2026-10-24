import Mathlib
import sympy.Basic
import Lemma.Definitions.Def_AlgebraicCurve_PlaceTaylorCoeff
import Lemma.Int.P2MUtil

open AlgebraicCurve

/--
[AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_AlgebraicCurve_IsConfluentPattern_exists_eq_of_lt_jetMult.lean)
-/
@[path]
private lemma main
  {K F : Type*} [Field K] [Field F] [Algebra K F]
  {M : ℕ}
  {P : Fin M → Place K F}
  {t : Fin M → F}
  {e : Fin M → ℕ}
  {i : Fin M}
  {q : ℕ}
-- given
  (hpat : IsConfluentPattern P t e)
  (hq : q < jetMult P (P i)) :
-- imply
  ∃ i', P i' = P i ∧ e i' = q := by
  classical
  obtain ⟨-, h2, h3⟩ := hpat
  set B : Finset (Fin M) := Finset.univ.filter (fun i' => P i' = P i) with hB
  have hcard : B.card = jetMult P (P i) := by
-- proof
    rw [hB]; unfold AlgebraicCurve.jetMult; convert rfl
  have hmaps : ∀ a (ha : a ∈ B), (fun a (_ : a ∈ B) => e a) a ha ∈ Finset.range (jetMult P (P i)) := by
    intro a ha
    have hPa : P a = P i := (Finset.mem_filter.mp ha).2
    rw [Finset.mem_range, ← hPa]; exact h3 a
  have hinj : ∀ a₁ a₂ (h₁ : a₁ ∈ B) (h₂ : a₂ ∈ B),
      (fun a (_ : a ∈ B) => e a) a₁ h₁ = (fun a (_ : a ∈ B) => e a) a₂ h₂ → a₁ = a₂ :=
    fun a₁ a₂ h₁ h₂ he =>
      h2 a₁ a₂ (((Finset.mem_filter.mp h₁).2).trans ((Finset.mem_filter.mp h₂).2).symm) he
  obtain ⟨a, ha, hqa⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a (_ : a ∈ B) => e a) hmaps hinj
    (by rw [Finset.card_range, hcard]) q (Finset.mem_range.mpr hq)
  exact ⟨a, (Finset.mem_filter.mp ha).2, hqa.symm⟩


-- created on 2026-10-23
