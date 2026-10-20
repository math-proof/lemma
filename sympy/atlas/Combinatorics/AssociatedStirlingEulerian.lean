/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/AssociatedStirlingEulerian.lean -/

import Mathlib.GroupTheory.Perm.Cycle.Type
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Finset.Card

namespace MetaMathlibExt

/-- Excedance count of a permutation of `Fin n`: the number of `i` with `σ i > i`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 130-132; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def excedanceCount (n : ℕ) (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter (fun i : Fin n => i < σ i)).card

/-- An `r`-minus-cycle permutation of `Fin n`: every cycle length is at most `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `1 ≤ r`, and every nontrivial entry of
`σ.cycleType` requires `≤ r`. The point condition is vacuous for `Fin 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 257-259;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRMinusAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → 1 ≤ r) ∧ ∀ m ∈ σ.cycleType.toFinset, m ≤ r

/-- An `r`-associated-cycle permutation of `Fin n`: every cycle length exceeds `r`.

Fixed one-cycles are omitted by `Equiv.Perm.cycleType`, so they are handled
explicitly: a fixed point requires `r < 1`, and every nontrivial entry of
`σ.cycleType` requires `r <` its length. The point condition is vacuous for
`Fin 0`, including when `r = 0`.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 106-108 and Lines 653-657;
URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def IsRAssociatedCyclePerm (r n : ℕ) (σ : Equiv.Perm (Fin n)) : Prop :=
  (∀ i, σ i = i → r < 1) ∧ ∀ m ∈ σ.cycleType.toFinset, r < m

instance (r n : ℕ) : DecidablePred (IsRMinusAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRMinusAssociatedCyclePerm; infer_instance

instance (r n : ℕ) : DecidablePred (IsRAssociatedCyclePerm r n) :=
  fun σ => by unfold IsRAssociatedCyclePerm; infer_instance

/-- The `r`-minus-associated Stirling Eulerian number `A^(r-minus)_(n,m)`:
the cardinality of permutations of `n` objects with all cycle lengths at most
`r` and exactly `m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 257-259; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rMinusAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRMinusAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

/-- The `r`-associated Stirling Eulerian number `A^r_(n,m)`: the cardinality of
permutations of `n` objects with all cycle lengths greater than `r` and exactly
`m` excedances.

Concept `jis_term_6573e30b9007548081ca6e28`; source JIS VOL28/Rakotoson/rakoto12.tex
Lines 653-657; URL https://cs.uwaterloo.ca/journals/JIS/VOL28/Rakotoson/rakoto12.tex. -/
def rAssociatedStirlingEulerian (r n m : ℕ) : ℕ :=
  ((Finset.univ.filter (IsRAssociatedCyclePerm r n)).filter
    (fun σ => excedanceCount n σ = m)).card

end MetaMathlibExt
