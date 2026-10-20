/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/CompleteGesselWord.lean -/

import sympy.atlas.NumberTheory.GesselWord
/-!
# Complete Gessel words

A complete Gessel word is a Gessel word in which each letter occurs as often as its
barred counterpart.

## References

- [A. Ayyer, *Towards a Human Proof of Gessel's Conjecture*](https://cs.uwaterloo.ca/journals/JIS/VOL12/Ayyer/ayyer7.tex),
  Definition 3 (source statement `jis_b68f59060d4f5b144b4dc9e5`).
-/

namespace MetaMathlibExt

/-- A complete Gessel word over `S = [n]`: a Gessel word in which the unbarred and
barred occurrence counts agree for every letter. -/
def IsCompleteGesselWord (n : ℕ) (w : List (GesselAlphabet n)) : Prop :=
  IsGesselWord n w ∧
    ∀ i : Fin n,
      gesselUnbarredCount n w (i.val + 1) = gesselBarredCount n w (i.val + 1)

/-- A word is complete exactly when it is a Gessel word and every letter has zero
signed balance. -/
theorem isCompleteGesselWord_iff_balance_eq_zero (n : ℕ) (w : List (GesselAlphabet n)) :
    IsCompleteGesselWord n w ↔
      IsGesselWord n w ∧ ∀ i : Fin n, gesselBalance n w (i.val + 1) = 0 := by
  constructor
  · rintro ⟨hg, hcount⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hcount i
    unfold gesselBalance
    omega
  · rintro ⟨hg, hbalance⟩
    refine ⟨hg, fun i => ?_⟩
    have hi := hbalance i
    unfold gesselBalance at hi
    omega

end MetaMathlibExt
