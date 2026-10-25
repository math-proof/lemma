/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/LunnonDimensionDecomposition.lean -/

import Mathlib.Order.Interval.Finset.Nat
import Mathlib.SetTheory.Cardinal.NatCard
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star
import Mathlib.Data.Nat.Choose.Sum
import Def.Combinatorics.Enumerative.LunnonDimensionDecomposition.Part10


section

namespace MetaMathlibExt

open scoped BigOperators

/-- Lunnon's dimension-decomposition formula for fixed polycubes, corrected
domain `1 < n`: `A_d(n) = ∑_{i=1}^{n-1} C(d,i) * DX(n,i)`.

Sources: Sebastian Luther and Stephan Mertens, *The Perimeter of Proper
Polycubes*, Journal of Integer Sequences 20 (2017), Article 17.9.5,
<https://cs.uwaterloo.ca/journals/JIS/VOL20/Mertens/mert4.tex>:
Lunnon's classical formula `eq:lunnon-a`, lines 172–175, with sum
`i = 1, …, n-1` and factor `C(d,i)`; `DX` notation and the at-most-`n-1`
dimensions bound, lines 163–166. Original: W. F. Lunnon, *Counting
multidimensional polyominoes*, Comput. J. 18 (1975), 366–367.
`DX(n,0) = 0` for `n > 1` from Asinowski–Barequet–Barequet–Rote, JIS 15
(2012), Article 12.8.4, line 978,
<https://cs.uwaterloo.ca/journals/JIS/VOL15/Barequet/barequet2.tex>.

The `1 < n` restriction is required because the printed display omits its
`n`-domain and is false at `n = 1`: the one-cell polycube is zero-dimensional,
so it is counted by the `i = 0` term, which the sum over `Ico 1 n` excludes.
On `n > 1` the `i = 0` term vanishes by `DX(n,0) = 0`, making the omission
valid exactly on this domain. No claim is made for `n = 1`.

Proves `Wanted` entry `lunnon_fixed_polycube_dimension_decomposition`.
-/
theorem lunnon_fixed_polycube_dimension_decomposition
    (d n : ℕ) (hn : 1 < n) :
    fixedPolycubeCount d n =
      Finset.sum (Finset.Ico 1 n) (fun i => Nat.choose d i * properFixedPolycubeCount n i) := by
  have hbase : fixedPolycubeCount d n =
      ∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m := by
    unfold fixedPolycubeCount
    rw [card_eq_sum_fiber_aux, sum_fiber_eq_range_aux]
  have hM1 : d + 1 ≤ max (d + 1) n := Nat.le_max_left _ _
  have hM2 : n ≤ max (d + 1) n := Nat.le_max_right _ _
  have hLHS : (∑ m ∈ Finset.range (d + 1), d.choose m * properFixedPolycubeCount n m) =
      ∑ m ∈ Finset.range (max (d + 1) n), d.choose m * properFixedPolycubeCount n m := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_range] at hx ⊢
      omega
    · intro m hm1 hm2
      simp only [Finset.mem_range] at hm1 hm2
      have hdm : d < m := by omega
      rw [Nat.choose_eq_zero_of_lt hdm, Nat.zero_mul]
  have hRHS : (∑ i ∈ Finset.Ico 1 n, d.choose i * properFixedPolycubeCount n i) =
      ∑ m ∈ Finset.range (max (d + 1) n), d.choose m * properFixedPolycubeCount n m := by
    apply Finset.sum_subset
    · intro x hx
      simp only [Finset.mem_Ico, Finset.mem_range] at hx ⊢
      omega
    · intro m hm1 hm2
      simp only [Finset.mem_range, Finset.mem_Ico] at hm1 hm2
      by_cases h1 : 1 ≤ m
      · have hge : n ≤ m := by
          rcases Nat.lt_or_ge m n with h | h
          · exact absurd ⟨h1, h⟩ hm2
          · exact h
        rw [vanish_DX_ge_aux n m hge, mul_zero]
      · have hm0 : m = 0 := by omega
        subst hm0
        rw [vanish_DX_zero_aux n hn, mul_zero]
  rw [hbase, hLHS, ← hRHS]

end MetaMathlibExt
end
