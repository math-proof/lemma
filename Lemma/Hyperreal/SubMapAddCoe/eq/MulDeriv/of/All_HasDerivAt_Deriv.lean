import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Hyperreal
import Initialize.Tactic.Attr.Basic
open Filter Hyperreal


@[path]
private lemma main
  {g : ℝ → ℝ}
  {x : ℝ}
  {Δx : ℝ*}
-- given
  (hg : ∀ y, HasDerivAt g (deriv g x) y) :
-- imply
  (show ℝ* from Germ.map g ((x : ℝ*) + Δx)) - ↑(g x) = ↑(deriv g x) * Δx := by
-- proof
  set c : ℝ := deriv g x
  have hinc : ∀ t : ℝ, g (x + t) - g x = c * t := by
    intro t
    have hderiv : ∀ y, deriv (fun s : ℝ => g s - c * s) y = 0 := by
      intro y
      rw [deriv_fun_sub (hg y).differentiableAt (differentiableAt_fun_id.const_mul c)]
      rw [deriv_const_mul c differentiableAt_fun_id]
      have hgy : deriv g y = c := by
        simpa [c] using (hg y).deriv
      rw [hgy, congrFun deriv_id'' y]
      ring
    have hdiff : Differentiable ℝ (fun s : ℝ => g s - c * s) := by
      intro y
      exact ((hg y).differentiableAt).fun_sub (differentiableAt_fun_id.const_mul c)
    have heq := is_const_of_deriv_eq_zero hdiff hderiv (x + t) x
    calc
      _ = (g (x + t) - c * (x + t)) - (g x - c * x) + (c * (x + t) - c * x) := by
        ring
      _ = c * (x + t) - c * x := by
        rw [heq, sub_self, zero_add]
      _ = c * t := by
        ring
  refine Germ.inductionOn Δx fun d => ?_
  change (
      Germ.map g ((↑x : Germ (hyperfilter ℕ : Filter ℕ) ℝ) + (↑d : Germ (hyperfilter ℕ : Filter ℕ) ℝ)) -
        (↑(g x) : Germ (hyperfilter ℕ : Filter ℕ) ℝ) =
        (↑c : Germ (hyperfilter ℕ : Filter ℕ) ℝ) * (↑d : Germ (hyperfilter ℕ : Filter ℕ) ℝ))
  have hx : (↑x : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => x) := rfl
  have hgx : (↑(g x) : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => g x) := rfl
  have hc : (↑c : Germ (hyperfilter ℕ : Filter ℕ) ℝ) = ↑(fun _ : ℕ => c) := rfl
  rw [hx, hgx, hc, (Germ.coe_add (fun _ : ℕ => x) d).symm, Germ.map_coe]
  have hcomp : g ∘ ((fun _ : ℕ => x) + d) = fun n => g (x + d n) := by
    funext n
    rfl
  rw [hcomp, (Germ.coe_sub (fun n : ℕ => g (x + d n)) (fun _ : ℕ => g x)).symm,
    (Germ.coe_mul (fun _ : ℕ => c) d).symm]
  apply Germ.coe_eq.mpr
  refine Eventually.of_forall fun n => ?_
  exact hinc (d n)


-- created on 2026-11-04
