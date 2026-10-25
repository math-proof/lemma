/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/HilbertWaring.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, @toskua, Avocado, Codex
-/

import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Def.Combinatorics.Schnirelmann
import Lemma.Finset.Schnirelmann
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.PSeries
import Mathlib.Data.Int.CardIntervalMod
import Mathlib.Data.Int.NatAbs
import Mathlib.Data.Finset.Max
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic
import Abbrev.NumberTheory.HilbertWaring.Part2
/-!
# Hilbert–Waring theorem

This file proves the Hilbert–Waring theorem by Linnik's elementary method. It develops
divisor-counting estimates and an inductive mean-value bound for polynomial Weyl sums, then
combines them with Schnirelmann's sumset inequality to obtain a finite additive basis of power sums.
-/


namespace MathlibExt.NumberTheory.HilbertWaringWanted

open Finset

open scoped Pointwise

def hwPairVal (H M : ℕ) (p : hwPairData H M) : ℤ :=
  hwSignedVal H p.1.1 * hwCentered M p.2.1 +
    hwSignedVal H p.1.2 * hwCentered M p.2.2

def hwPairCount (H M : ℕ) (n : ℤ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M)).filter fun p ↦ hwPairVal H M p = n)

def hwFourTermCount (H M : ℕ) : ℕ :=
  #((Finset.univ : Finset (hwPairData H M × hwPairData H M)).filter fun p ↦
    hwPairVal H M p.1 + hwPairVal H M p.2 = 0)

def hwCenteredFourTerm (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    ∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0

def hwCenteredFourNonzero (H M : ℕ) :
    Finset ((Fin 4 → Fin (2 * H + 1)) × (Fin 4 → Fin (2 * M + 1))) :=
  Finset.univ.filter fun p ↦
    (∑ i, hwCentered H (p.1 i) * hwCentered M (p.2 i) = 0) ∧
      ∀ i, hwCentered H (p.1 i) ≠ 0

def hwPackCenteredNonzero (H M : ℕ)
    (p : {p // p ∈ hwCenteredFourNonzero H M}) :
    hwPairData H M × hwPairData H M :=
  let s : Fin 4 → hwSigned H := fun i ↦
    (hwSignedEquivCentered H).symm
      ⟨p.1.1 i, (Finset.mem_filter.mp p.2).2.2 i⟩
  (((s 0, s 1), (p.1.2 0, p.1.2 1)),
    ((s 2, s 3), (p.1.2 2, p.1.2 3)))

end MathlibExt.NumberTheory.HilbertWaringWanted
