/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch5Entry4.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Analysis.SpecificLimits.Normed
/-!
# Ramanujan's Notebooks, Part I, Chapter 5, Entry 4

Eulerian polynomial: Ψₙ(p)/(p+1)ⁿ⁺¹ equals Σ(k+1)ⁿ(-p)ᵏ.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch5

namespace Entry4

open scoped Nat Real BigOperators Interval Polynomial

open Asymptotics Filter Finset Complex Topology

noncomputable section

def chapter5Entry4Term (n : ℕ) (p : ℂ) (k : ℕ) : ℂ :=
  (k + 1 : ℂ) ^ n * (-p) ^ k

def eulerianNumber : ℕ → ℕ → ℕ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | n + 1, k =>
      (k + 1) * eulerianNumber n k +
        (n + 1 - k) *
          (if k = 0 then 0 else eulerianNumber n (k - 1))

def chapter5Psi {R : Type*} [CommRing R] (n : ℕ) (p : R) : R :=
  if n = 0 then 1
  else ∑ k ∈ range n, (eulerianNumber n k : R) * (-p) ^ k

end
end Entry4
end MathlibExt.Analysis.Ramanujan.Part1Ch5
