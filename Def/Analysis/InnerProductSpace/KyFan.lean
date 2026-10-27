import Mathlib.Analysis.InnerProductSpace.Spectrum
import Mathlib.Analysis.Matrix.Hermitian
/-!
# Ky Fan eigenvalue inequality

For Hermitian `A, B`, sum of `k` largest eigenvalues of `A + B` ≤ sum
for `A` plus sum for `B`.

Source: Ky Fan, On a theorem of Weyl concerning eigenvalues of linear
transformations. I, PNAS 35 (1949), 652-655, DOI 10.1073/pnas.35.11.652.
-/


namespace InnerProductSpace.KyFanWanted

open scoped BigOperators

/-- The sum of the first `k` entries of `eig : Fin n → ℝ`. Applied to the eigenvalues of a
Hermitian matrix, listed in decreasing order, it is the sum of the `k` largest ones. -/
noncomputable def eigPrefSum {n : ℕ} (eig : Fin n → ℝ) (k : ℕ)
    (hk : k ≤ n) : ℝ :=
  ∑ i ∈ Finset.range k, if hi : i < k then eig (Fin.castLE hk ⟨i, hi⟩) else 0

end InnerProductSpace.KyFanWanted
