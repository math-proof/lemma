import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Polynomial.DumasIrreducibilityCriterion
open MetaMathlibExt


/--
[irreducible_of_dumas_padic_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Polynomial/DumasIrreducibilityCriterion.lean)
-/
@[path]
private lemma irreducible_of_dumas_padic_criterion_eq
  {p : ℕ}
  {f : Polynomial ℤ}
-- given
  (hp : Nat.Prime p)
  (hdeg : 0 < f.natDegree)
  (h0 : f.coeff 0 ≠ 0)
  (hlead : f.coeff f.natDegree ≠ 0)
  (hno_int : ∀ k : ℕ, 1 < k → k ∣ f.natDegree → ¬ (k : ℤ) ∣ padicValRat p ((f.coeff 0 : ℤ) : ℚ) - padicValRat p ((f.coeff f.natDegree : ℤ) : ℚ))
  (hline : ∀ i : ℕ, i ≤ f.natDegree → f.coeff i ≠ 0 → (f.natDegree : ℤ) * padicValRat p ((f.coeff i : ℤ) : ℚ) ≥ ((f.natDegree - i : ℕ) : ℤ) * padicValRat p ((f.coeff 0 : ℤ) : ℚ) + (i : ℤ) * padicValRat p ((f.coeff f.natDegree : ℤ) : ℚ)) :
-- imply
  Irreducible (f.map (Int.castRingHom ℚ)) := by
-- proof
  apply MetaMathlibExt.irreducible_of_dumas_padic_criterion p hp f hdeg h0 hlead hno_int hline


-- created on 2026-10-20
