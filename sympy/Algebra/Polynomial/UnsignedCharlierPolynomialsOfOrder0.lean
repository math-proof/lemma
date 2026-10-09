import Mathlib.RingTheory.Polynomial.Pochhammer

namespace MetaMathlibExt

/-- Unsigned Charlier polynomials of order 0.

Terminating expansion `∑ k ∈ Finset.range (n + 1), (n.choose k) • ascPochhammer R k`
for `2F_0(-n, x; -1)`, an unsigned version of the Charlier polynomials of order 0.
The coefficient array is the exponential Riordan array `[e^x, ln(1/(1-x))]`. -/
noncomputable def unsignedCharlierOrder0 (R : Type*) [Semiring R] (n : ℕ) : Polynomial R :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) • ascPochhammer R k

/-- Natural coefficient array from coefficients of `ascPochhammer`. -/
noncomputable def unsignedCharlierCoeff (n m : ℕ) : ℕ :=
  ∑ k ∈ Finset.range (n + 1), (n.choose k) * (ascPochhammer ℕ k).coeff m

/-- General coefficient equality for the natural rows. -/
theorem unsignedCharlier_coeff_eq (n m : ℕ) :
    (unsignedCharlierOrder0 ℕ n).coeff m = unsignedCharlierCoeff n m := by
  simp [unsignedCharlierOrder0, unsignedCharlierCoeff]

end MetaMathlibExt
