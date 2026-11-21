import Def.Data.Vector.Functions
import Instance.Data.Pi.Sub
import Lemma.Real.Grad.Softmax.eq.Mul.Softmax
import Syntax.Analysis.Calculus.Deriv.Operators
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
open Real
open scoped Matrix


/--
The gradient of softmax with respect to a scalar input. The gradient of
output component `j` is its softmax weight times the difference between the
derivative of logit `j` and the softmax-weighted sum of the logit derivatives.
-/
@[path]
private lemma main
  {n : ℕ}
  {F : ℝ → (Fin n → ℝ)}
  {x : ℝ}
-- given
  (h₀ : DifferentiableAt ℝ F x) :
-- imply
  ∂[x] (F x).softmax =
    (F x).softmax • (∂[x] F x - (F x).softmax ⬝ᵥ ∂[x] F x) := by
-- proof
  have h := differentiableAt_pi.mp h₀
  have hexp (z : ℝ) : Exp.exp z = z.exp := rfl
  have hsm : ∀ j, DifferentiableAt ℝ (fun y => (F y).softmax j) x := by
    intro j
    simp only [Function.softmax, hexp]
    have hpos : 0 < ∑ i : Fin n, rexp (F x i) :=
      Finset.sum_pos (fun i _ => Real.exp_pos (F x i)) ⟨j, Finset.mem_univ j⟩
    convert ((h j).exp).div
      (DifferentiableAt.sum (u := Finset.univ) (fun i _ => (h i).exp))
      (by simpa using hpos.ne') using 2
    simp
  rw [deriv_pi hsm, deriv_pi h]
  funext j
  simp only [hexp, Function.softmax, dotProduct, Pi.mul_apply, smul_eq_mul,
    Pi.sub_scalar_apply]
  exact stack (F := fun i y => F y i) h j


-- created on 2023-03-18
-- updated on 2026-11-21
