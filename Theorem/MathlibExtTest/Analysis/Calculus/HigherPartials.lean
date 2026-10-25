/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Calculus/HigherPartials.lean -/


import Theorem.Analysis.Calculus.HigherPartials
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
open MetaMathlibExt


-- A continuous linear functional has the expected constant coordinate partial.
example {n : ℕ} (L : (Fin n → ℝ) →L[ℝ] ℝ) (i : Fin n) (x : Fin n → ℝ) :
    partialDeriv L i x = L (Pi.single i (1 : ℝ)) := by
  rw [partialDeriv_eq_fderiv_apply L i x L.differentiableAt]
  exact DFunLike.congr_fun L.hasFDerivAt.fderiv (Pi.single i (1 : ℝ))

-- Direct computation of the 1-after-0 mixed partial gives 2 * x 0.
example (x : Fin 2 → ℝ) :
    partialDeriv (partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1) 0) 1 x =
      2 * x 0 := by
  have hfirst :
      partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1) 0 =
        fun y => 2 * y 0 * y 1 := by
    funext y
    rw [partialDeriv_spec]
    have h := HasDerivAt.mul_const
      (HasDerivAt.pow ((hasDerivAt_id (𝕜 := ℝ) 0).const_add (y 0)) 2) (y 1)
    convert h.deriv using 1 <;> simp
  rw [hfirst, partialDeriv_spec]
  have h := HasDerivAt.const_mul (2 * x 0)
    ((hasDerivAt_id (𝕜 := ℝ) 0).const_add (x 1))
  convert h.deriv using 1 <;> simp

-- Clairaut's theorem turns the computed 1-after-0 order into the 0-after-1 order.
example (x : Fin 2 → ℝ) :
    partialDeriv (partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1) 1) 0 x =
      2 * x 0 := by
  rw [iterated_partialDeriv_commute
    (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1) 1 0 x (by fun_prop)]
  have hfirst :
      partialDeriv (fun y : Fin 2 → ℝ => y 0 ^ 2 * y 1) 0 =
        fun y => 2 * y 0 * y 1 := by
    funext y
    rw [partialDeriv_spec]
    have h := HasDerivAt.mul_const
      (HasDerivAt.pow ((hasDerivAt_id (𝕜 := ℝ) 0).const_add (y 0)) 2) (y 1)
    convert h.deriv using 1 <;> simp
  rw [hfirst, partialDeriv_spec]
  have h := HasDerivAt.const_mul (2 * x 0)
    ((hasDerivAt_id (𝕜 := ℝ) 0).const_add (x 1))
  convert h.deriv using 1 <;> simp

