import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.HowardPotentialPolynomial
open scoped BigOperators
open MetaMathlibExt


/--
[howard_potentialPolynomial_rTwo_eq_partialBell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HowardPotentialPolynomial.lean)
-/
@[path]
private lemma howard_potentialPolynomial_rTwo_eq_partialBell_eq
  {G : ℕ → Polynomial Rat}
  {n : ℕ}
-- given
  (hdeg : (G n).natDegree ≤ n)
  (heval : ∀ m : ℕ, m ≤ n → (G n).eval (↑m : Rat) = (n.factorial : Rat) * PowerSeries.coeff n ((PowerSeries.inv (PowerSeries.mk (fun k => (2 : Rat) / (((k + 2).factorial : Rat))))) ^ m)) :
-- imply
  G n = Finset.sum (Finset.range (n + 1)) (fun i =>
    Polynomial.C (((-1 : Rat) ^ i) * ((2 : Rat) ^ i) *
    (((n.factorial : Rat) * (i.factorial : Rat)) / (((n + 2 * i).factorial : Rat)))) *
    ((ascPochhammer Rat i) * Polynomial.C (((i.factorial : Rat))⁻¹)) *
    (((descPochhammer Rat (n - i)).comp (Polynomial.X + Polynomial.C (n : Rat))) *
    Polynomial.C ((((n - i).factorial : Rat))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + 2 * i) i
    (fun j => if 2 ≤ j then (1 : Rat) else 0))) := by
-- proof
  apply MetaMathlibExt.howard_potentialPolynomial_rTwo_eq_partialBell G n hdeg heval

/--
[howard_potentialPolynomial_eq_partialBell](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/HowardPotentialPolynomial.lean)
-/
@[path]
private lemma howard_potentialPolynomial_eq_partialBell_eq
  [Field K] [CharZero K]
  {r n : ℕ}
  {a : ℕ → K}
  {P : Polynomial K}
-- given
  (hr : 1 ≤ r)
  (har : a r ≠ 0)
  (hdeg : P.natDegree ≤ n)
  (heval : ∀ m : ℕ, m ≤ n → P.eval (↑m : K) = (n.factorial : K) * PowerSeries.coeff n ((PowerSeries.inv (PowerSeries.mk (fun k => (r.factorial : K) * a (r + k) / (a r * ((r + k).factorial : K))))) ^ m)) :
-- imply
  P = Finset.sum (Finset.range (n + 1)) (fun i =>
    Polynomial.C (((-1 : K) ^ i) * (((r.factorial : K) / a r) ^ i) *
    (((n.factorial : K) * (i.factorial : K)) / (((n + r * i).factorial : K)))) *
    ((ascPochhammer K i) * Polynomial.C (((i.factorial : K))⁻¹)) *
    (((descPochhammer K (n - i)).comp (Polynomial.X + Polynomial.C (n : K))) *
    Polynomial.C ((((n - i).factorial : K))⁻¹)) *
    Polynomial.C (MetaMathlibExt.partialBellPolynomial (n + r * i) i
    (fun j => if r ≤ j then a j else 0))) := by
-- proof
  apply MetaMathlibExt.howard_potentialPolynomial_eq_partialBell r n hr a har P hdeg heval


-- created on 2026-10-20
