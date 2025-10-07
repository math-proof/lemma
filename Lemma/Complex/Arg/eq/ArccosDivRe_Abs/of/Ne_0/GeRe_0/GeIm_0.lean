import Lemma.Complex.Arg.eq.Ite__Ite_Arcsin
import Lemma.Algebra.Div.ge.Zero.of.Ge_0.Ge_0
import Lemma.Algebra.SquareDiv.eq.DivSquareS
import Lemma.Algebra.GeNorm_0
open Algebra Complex


@[main]
private lemma main
  {z : ℂ}
-- given
  (h : z ≠ 0)
  (h_GeRe_0 : re z ≥ 0)
  (h_GeIm_0 : im z ≥ 0) :
-- imply
  arg z = arccos (re z / ‖z‖) := by
-- proof
  rw [Arg.eq.Ite__Ite_Arcsin]
  simp [h_GeRe_0]
  have h_Ge_0 := GeNorm_0 (a := z)
  have h_GeDiv__0 := Div.ge.Zero.of.Ge_0.Ge_0 h_GeRe_0 h_Ge_0
  have h_EqArccos := Real.arccos_eq_arcsin h_GeDiv__0
  rw [SquareDiv.eq.DivSquareS] at h_EqArccos
  sorry


-- created on 2025-01-13
-- updated on 2025-04-02
