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

end MetaMathlibExt
