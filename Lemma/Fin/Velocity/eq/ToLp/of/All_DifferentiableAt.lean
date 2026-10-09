import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.FDeriv.Linear
import Mathlib.Analysis.InnerProductSpace.PiL2
import sympy.physics.vector.kinematics
import sympy.Basic
open scoped ENNReal


/--
Cartesian decomposition of velocity: if
\(\vec{r}(t)=\sum_i x_i(t)\,\hat{e}_i\), then
\(\vec{v}(t)=\sum_i \dot{x}_i(t)\,\hat{e}_i\).
-/
@[path]
private lemma main
  {d : ℕ}
  {x : Fin d → ℝ → ℝ}
  {t : ℝ}
-- given
  (hx : ∀ i, DifferentiableAt ℝ (x i) t) :
-- imply
  velocity (fun s => WithLp.toLp 2 (fun i => x i s)) t =
    WithLp.toLp 2 (fun i => deriv (x i) t) := by
-- proof
  let e := (WithLp.linearEquiv (2 : ℝ≥0∞) ℝ (Fin d → ℝ)).toContinuousLinearEquiv
  have hpi : HasDerivAt (fun s => fun i => x i s) (fun i => deriv (x i) t) t :=
    hasDerivAt_pi.2 fun i => (hx i).hasDerivAt
  have hpath :
      (fun s => WithLp.toLp 2 (fun i => x i s)) = fun s => e.symm (fun i => x i s) := by
    funext s
    rfl
  have htarget :
      WithLp.toLp 2 (fun i => deriv (x i) t) = e.symm (fun i => deriv (x i) t) := rfl
  have h := e.symm.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt t hpi
  simp only [velocity, hpath, htarget]
  exact h.deriv


-- created on 2026-09-28
