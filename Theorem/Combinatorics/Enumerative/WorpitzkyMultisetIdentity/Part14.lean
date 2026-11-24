module
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Prod.Lex
public import Mathlib.Data.Multiset.Sort
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.Fintype.Vector
public import Mathlib.Data.Multiset.Count
public import Mathlib.Data.Multiset.Filter
public import Mathlib.Data.Fintype.Fin
public import Def.Combinatorics.Enumerative.WorpitzkyMultisetIdentity.Part14


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/WorpitzkyMultisetIdentity.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
section

namespace MetaMathlibExt

/-- Worpitzky identity for multiset Eulerian numbers: for nonnegative integers
`k` over `Fin m` with total `K`, `∏ i, C (x + k i - 1) (k i)` equals
`∑ p, C (x + K - p) K * a p` where `a p` counts permutations of the multiset
`1 ^ (k 1) ⋯ m ^ (k m)` with `p - 1` descents (summed over
`Finset.Icc 1 (max 1 K)`).

Source: A. Dzhumadil'daev and D. Yeliussizov, *Power Sums of Binomial
Coefficients*, Journal of Integer Sequences 16 (2013), Article 13.1.4, Theorem
Worpitzky, lines 212-217,
<https://cs.uwaterloo.ca/journals/JIS/VOL16/Yeliussizov/dzhuma6.tex>, quoting
A. S. Dzhumadil'daev, *Worpitzky identity for multipermutations*, Mat. Zametki
90 (2011), 464-466.

Proves `Wanted` entry `worpitzky_identity_multiset`.
-/
theorem worpitzky_identity_multiset (m : ℕ) (k : Fin m → ℕ) (x : ℕ) :
    Finset.prod Finset.univ (fun i => Nat.choose (x + k i - 1) (k i)) =
      Finset.sum (Finset.Icc 1 (max 1 (Finset.sum Finset.univ (fun a => k a)))) (fun p =>
        Nat.choose (x + Finset.sum Finset.univ (fun a => k a) - p)
            (Finset.sum Finset.univ (fun a => k a)) *
          Nat.card { w : Fin (Finset.sum Finset.univ (fun a => k a)) → Fin m //
            (∀ i,
              Fintype.card
                  { j : Fin (Finset.sum Finset.univ (fun a => k a)) // w j = i } = k i) ∧
            (Finset.univ.filter
                (fun j : Fin (Finset.sum Finset.univ (fun a => k a)) =>
                  ∃ h : j.val + 1 < Finset.sum Finset.univ (fun a => k a),
                    w j > w ⟨j.val + 1, h⟩)).card + 1 = p }) := by
  rw [wmi_lhs_eq_word_sum]
  change (∑ w : wmiWords m k,
    Nat.choose (x + (∑ i, k i) - wmiDesClass w.1) (∑ i, k i)) = _
  rw [wmi_regroup]
  apply Finset.sum_congr rfl
  intro p _
  rw [wmi_word_fiber_card]

end MetaMathlibExt
end
