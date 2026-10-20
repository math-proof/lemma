import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.PrimeCounting.DirichletDensityArithmeticProgression
open Topology Filter
open Complex LSeries
open Complex LSeries ArithmeticFunction
open Complex LSeries ArithmeticFunction.vonMangoldt
open MetaMathlibExt.NumberTheory.PrimeCounting


/--
[dirichlet_density_primes_arithmetic_progression](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/PrimeCounting/DirichletDensityArithmeticProgression.lean)
-/
@[path]
private lemma dirichlet_density_primes_arithmetic_progression_eq
  {a m : ℕ}
-- given
  (hm : 0 < m)
  (hcop : Nat.Coprime a m) :
-- imply
  Filter.Tendsto (fun s : ℝ =>
    (∑' (p : { p : ℕ // Nat.Prime p ∧ p ≡ a [MOD m] }), (p.val : ℝ) ^ (-s)) /
    (∑' (p : { p : ℕ // Nat.Prime p }), (p.val : ℝ) ^ (-s)))
    (nhdsWithin 1 (Set.Ioi 1)) (nhds (1 / (Nat.totient m : ℝ))) := by
-- proof
  apply MetaMathlibExt.NumberTheory.PrimeCounting.dirichlet_density_primes_arithmetic_progression a m hm hcop


-- created on 2026-10-20
