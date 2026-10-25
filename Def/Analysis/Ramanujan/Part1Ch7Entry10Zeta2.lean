/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Ramanujan/Part1Ch7Entry10Zeta2.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Meromorphic.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Def.Analysis.Ramanujan.Part1Ch7Entry10ZetaSide
import Lemma.Real.Ramanujan.Part1Ch7Entry10ZetaSide
import Lemma.Complex.Part1Ch7PowerDifference
import Def.Analysis.Ramanujan.Part1Ch7PowerDifference
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Meromorphic.Complex
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.Topology.Separation.CompletelyRegular
/-!
# Ramanujan's Notebooks, Part I, Chapter 7, Entry 10

Power-sum distribution relation equals (1-nʳ⁺¹)ζ(-r) meromorphically.
-/


namespace MathlibExt.Analysis.Ramanujan.Part1Ch7

namespace Entry10Zeta2

open scoped Nat Real BigOperators Interval Polynomial ContDiff

open Asymptotics Filter Finset Complex Topology MeasureTheory

noncomputable section

def chapter7Entry10DistributionLeft
    (phi : ℂ → ℂ → ℂ) (n : ℕ) (x r : ℂ) : ℂ :=
  phi r x - Complex.cpow (n : ℂ) r *
    ∑ k ∈ range n, phi r ((x - k) / n)

export Entry10Zeta4 (chapter7Entry10ZetaSide)

noncomputable def ch7Reindex (n : ℕ) (hn : 0 < n) : Fin n × ℕ ≃ ℕ where
  toFun p := n * p.2 + (n - 1 - p.1.val)
  invFun m := (⟨n - 1 - m % n, by have h := Nat.mod_lt m hn; omega⟩, m / n)
  left_inv := by
    rintro ⟨k, j⟩
    have hkn : k.val < n := k.isLt
    have ht : n - 1 - k.val < n := by omega
    have hmod : (n * j + (n - 1 - k.val)) % n = n - 1 - k.val := by
      rw [show n * j + (n - 1 - k.val) = (n - 1 - k.val) + n * j from by ring,
        Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt ht]
    have hdiv : (n * j + (n - 1 - k.val)) / n = j := by
      rw [show n * j + (n - 1 - k.val) = (n - 1 - k.val) + n * j from by ring,
        Nat.add_mul_div_left _ _ hn, Nat.div_eq_of_lt ht, zero_add]
    refine Prod.ext (Fin.ext ?_) hdiv
    show n - 1 - (n * j + (n - 1 - k.val)) % n = k.val
    rw [hmod]
    omega
  right_inv := by
    intro m
    have ht : m % n < n := Nat.mod_lt m hn
    have hsub : n - 1 - (n - 1 - m % n) = m % n := by omega
    show n * (m / n) + (n - 1 - (n - 1 - m % n)) = m
    rw [hsub]
    exact Nat.div_add_mod m n

end
end Entry10Zeta2
end MathlibExt.Analysis.Ramanujan.Part1Ch7
