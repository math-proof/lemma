import Lemma.Algebra.EqRe_0.of.Eq_0
import Lemma.Algebra.EqIm_0.of.Eq_0
import Lemma.Complex.Eq_0.of.EqRe_0.EqIm_0
open Algebra Complex


@[main]
private lemma main
  {z : ℂ} :
-- imply
  z = 0 ↔ re z = 0 ∧ im z = 0 := by
-- proof
  constructor
  intro h_Eq_0
  exact ⟨EqRe_0.of.Eq_0 h_Eq_0, EqIm_0.of.Eq_0 h_Eq_0⟩
  intro ⟨h_Re, h_Im⟩
  apply Eq_0.of.EqRe_0.EqIm_0 <;> assumption


-- created on 2025-01-17
