/-
Author: @akiezun, Avocado
-/

import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Tactic.NormNum.Parity
/-!
# Ramanujan's Notebooks, Part I, Chapter 8

Statements of entries from B. C. Berndt, *Ramanujan's Notebooks, Part I*
(Springer, 1985), with proofs.
-/


section

namespace Ramanujan.Part1Ch8

namespace Entry16Eulerconstantseries

open scoped BigOperators Real

open Topology

noncomputable section

def Afun : ℕ → ℕ := fun k => (3 ^ k - 1) / 2

def Hsum : ℕ → ℝ := fun n => ∑ i ∈ Finset.Icc 1 n, ((i : ℝ))⁻¹

def gfun : ℕ → ℝ := fun j => (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))

def Tfun : ℕ → ℝ := fun k =>
  ((k + 1 : ℕ) : ℝ) *
    ∑ j ∈ Finset.Icc (Afun k + 1) (Afun (k + 1)),
      (1 : ℝ) / ((3 * (j : ℝ)) ^ 3 - 3 * (j : ℝ))

end
end Entry16Eulerconstantseries
end Ramanujan.Part1Ch8
end
