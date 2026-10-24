/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/Combinatorics/Enumerative/RiordanAZSequences.lean -/


import sympy.atlas.Combinatorics.Enumerative.RiordanAZSequences
import Lemma.Finset.Enumerative.RiordanAZSequences

namespace MetaMathlibExt

-- The forward implication recovers the Riordan normalization.
example (d : ℕ → ℕ → ℤ) (htri : ∀ n k : ℕ, n < k → d n k = 0)
    (g f : PowerSeries ℤ) (hg0 : PowerSeries.constantCoeff g = 1)
    (hf0 : PowerSeries.constantCoeff f = 0) (hf1 : PowerSeries.coeff 1 f ≠ 0)
    (hd : ∀ n k : ℕ, d n k = PowerSeries.coeff n (g * f ^ k)) : d 0 0 = 1 := by
  rcases (riordan_iff_AZ_sequences d htri).mp ⟨g, f, hg0, hf0, hf1, hd⟩ with
    ⟨_, _, _, hd00, _, _⟩
  exact hd00

-- The backward implication reconstructs the two power series.
example (d : ℕ → ℕ → ℤ) (htri : ∀ n k : ℕ, n < k → d n k = 0)
    (A Z : ℕ → ℚ) (hA0 : A 0 ≠ 0) (hd00 : d 0 0 = 1)
    (hA : ∀ n k : ℕ, (d (n + 1) (k + 1) : ℚ) =
      ∑ j ∈ Finset.range (n + 1), A j * d n (k + j))
    (hZ : ∀ n : ℕ, (d (n + 1) 0 : ℚ) =
      ∑ j ∈ Finset.range (n + 1), Z j * d n j) :
    ∃ g f : PowerSeries ℤ, PowerSeries.constantCoeff g = 1 ∧
      PowerSeries.constantCoeff f = 0 ∧ PowerSeries.coeff 1 f ≠ 0 ∧
      ∀ n k : ℕ, d n k = PowerSeries.coeff n (g * f ^ k) := by
  exact (riordan_iff_AZ_sequences d htri).mpr ⟨A, Z, hA0, hd00, hA, hZ⟩

end MetaMathlibExt
