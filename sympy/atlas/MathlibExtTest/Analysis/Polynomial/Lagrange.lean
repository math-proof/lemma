/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Analysis/Polynomial/Lagrange.lean -/


import sympy.atlas.Analysis.Polynomial.Lagrange


open Lagrange

-- Normal API use: the evaluated basis, Lebesgue function, and interpolant
-- accept nodes and elaborate at the expected types.
noncomputable example (x : Fin 3 → ℝ) (k : Fin 3) (t : ℝ) : ℝ :=
  Lagrange.evalBasis x k t

noncomputable example (x : Fin 3 → ℝ) (t : ℝ) : ℝ :=
  Lagrange.lebesgueFunction x t

noncomputable example (x : Fin 3 → ℝ) (f : ℝ → ℝ) (t : ℝ) : ℝ :=
  Lagrange.evalInterpolant x f t

-- Characteristic behavior: delta at nodes for injective node systems.
example (x : Fin 3 → ℝ) (hx : Function.Injective x) (k : Fin 3) :
    Lagrange.evalBasis x k (x k) = 1 :=
  Lagrange.evalBasis_self x hx k

example (x : Fin 3 → ℝ) (k j : Fin 3) (h : k ≠ j) :
    Lagrange.evalBasis x k (x j) = 0 :=
  Lagrange.evalBasis_of_ne x h

example (x : Fin 3 → ℝ) (hx : Function.Injective x) (f : ℝ → ℝ) (j : Fin 3) :
    Lagrange.evalInterpolant x f (x j) = f (x j) :=
  Lagrange.evalInterpolant_at_node x hx f j

example (x : Fin 3 → ℝ) (hx : Function.Injective x) (j : Fin 3) :
    Lagrange.lebesgueFunction x (x j) = 1 :=
  Lagrange.lebesgueFunction_at_node x hx j
