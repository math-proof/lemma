import Mathlib
import Initialize.Tactic.Attr.Basic
import Abbrev.v1.Atlas.NumberTheoryI.code.DirichletL
open Complex Filter Topology Nat DirichletLFunction
open scoped LSeries.notation


namespace DirichletLFunction

/--
[dirichletLFunction_eq_LSeries](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_eq_LSeries
  {N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  DirichletCharacter.LFunction χ s = LSeries (χ ·) s :=
-- proof
  DirichletCharacter.LFunction_eq_LSeries χ hs
@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_eq_dirichlet_series := dirichletLFunction_eq_LSeries

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLSeries_eulerProduct_hasProd](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLSeries_eulerProduct_hasProd
  {N : ℕ}
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  HasProd (fun p : Nat.Primes ↦ (1 - χ p * (p : ℂ) ^ (-s))⁻¹) (L ↗χ s) :=
-- proof
  DirichletCharacter.LSeries_eulerProduct_hasProd χ hs
@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product_hasProd := dirichletLSeries_eulerProduct_hasProd

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLSeries_eulerProduct_tprod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLSeries_eulerProduct_tprod
  {N : ℕ}
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  ∏' p : Nat.Primes, (1 - χ p * (p : ℂ) ^ (-s))⁻¹ = L ↗χ s :=
-- proof
  DirichletCharacter.LSeries_eulerProduct_tprod χ hs
@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product_tprod := dirichletLSeries_eulerProduct_tprod

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLSeries_eulerProduct](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLSeries_eulerProduct
  {N : ℕ}
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  Tendsto (fun n : ℕ ↦ ∏ p ∈ primesBelow n, (1 - χ p * (p : ℂ) ^ (-s))⁻¹) atTop (𝓝 (L ↗χ s)) :=
-- proof
  DirichletCharacter.LSeries_eulerProduct χ hs
@[deprecated (since := "2024-12-18")]
alias def_18_19_euler_product := dirichletLSeries_eulerProduct

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLFunction_differentiableAt](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_differentiableAt
  {N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  DifferentiableAt ℂ (DirichletCharacter.LFunction χ) s :=
-- proof
  DirichletCharacter.differentiableAt_LFunction χ s (Or.inl (by
    intro h; rw [h] at hs; simp at hs))
@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_holomorphic := dirichletLFunction_differentiableAt

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLSeries_ne_zero_of_one_lt_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLSeries_ne_zero_of_one_lt_re
  {N : ℕ}
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hs : 1 < s.re) :
-- imply
  L ↗χ s ≠ 0 :=
-- proof
  DirichletCharacter.LSeries_ne_zero_of_one_lt_re χ hs
@[deprecated (since := "2024-12-18")]
alias def_18_19_L_function_ne_zero_of_one_lt_re := dirichletLSeries_ne_zero_of_one_lt_re

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLFunction_modOne_eq_riemannZeta](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_modOne_eq_riemannZeta
  {χ : DirichletCharacter ℂ 1} :
-- imply
  DirichletCharacter.LFunction χ = riemannZeta :=
-- proof
  DirichletCharacter.LFunction_modOne_eq
@[deprecated (since := "2024-12-18")]
alias L_trivial_eq_zeta := dirichletLFunction_modOne_eq_riemannZeta

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLFunction_differentiable_of_ne_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_differentiable_of_ne_one
  {N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ N}
-- given
  (hχ : χ ≠ 1) :
-- imply
  Differentiable ℂ (DirichletCharacter.LFunction χ) :=
-- proof
  DirichletCharacter.differentiable_LFunction hχ
@[deprecated (since := "2024-12-18")]
alias prop_18_20_differentiable_LFunction := dirichletLFunction_differentiable_of_ne_one

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLFunction_ne_zero_at_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_ne_zero_at_one
  {N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ N}
-- given
  (hχ : χ ≠ 1) :
-- imply
  DirichletCharacter.LFunction χ 1 ≠ 0 :=
-- proof
  DirichletCharacter.LFunction_apply_one_ne_zero hχ
@[deprecated (since := "2024-12-18")]
alias thm_18_key_L_one_ne_zero := dirichletLFunction_ne_zero_at_one

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLFunction_ne_zero_of_one_le_re](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLFunction_ne_zero_of_one_le_re
  {N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ N}
  {s : ℂ}
-- given
  (hχs : χ ≠ 1 ∨ s ≠ 1)
  (hs : 1 ≤ s.re) :
-- imply
  DirichletCharacter.LFunction χ s ≠ 0 :=
-- proof
  DirichletCharacter.LFunction_ne_zero_of_one_le_re χ hχs hs
@[deprecated (since := "2024-12-18")]
alias thm_18_key_L_ne_zero_of_one_le_re := dirichletLFunction_ne_zero_of_one_le_re

end DirichletLFunction

namespace DirichletLFunction

/--
[infinite_primes_in_residueClass_zmod](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma infinite_primes_in_residueClass_zmod
  {q : ℕ}
  [NeZero q]
  {a : ZMod q}
-- given
  (ha : IsUnit a) :
-- imply
  {p : ℕ | p.Prime ∧ (p : ZMod q) = a}.Infinite :=
-- proof
  Nat.infinite_setOf_prime_and_eq_mod ha
@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_zmod := infinite_primes_in_residueClass_zmod

end DirichletLFunction

namespace DirichletLFunction

/--
[exists_prime_gt_and_zmodEq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma exists_prime_gt_and_zmodEq
  {n : ℕ}
  {q : ℕ}
  {a : ℤ}
-- given
  (hq : q ≠ 0)
  (h : IsCoprime a q) :
-- imply
  ∃ p > n, p.Prime ∧ ↑p ≡ a [ZMOD (q : ℤ)] :=
-- proof
  Nat.forall_exists_prime_gt_and_zmodEq n hq h
@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_int := exists_prime_gt_and_zmodEq

end DirichletLFunction

namespace DirichletLFunction

/--
[exists_prime_gt_and_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma exists_prime_gt_and_modEq
  {n : ℕ}
  {q a : ℕ}
-- given
  (hq : q ≠ 0)
  (h : a.Coprime q) :
-- imply
  ∃ p > n, p.Prime ∧ p ≡ a [MOD q] :=
-- proof
  Nat.forall_exists_prime_gt_and_modEq n hq h
@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet := exists_prime_gt_and_modEq

end DirichletLFunction

namespace DirichletLFunction

/--
[infinite_primes_in_arithmeticProgression](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma infinite_primes_in_arithmeticProgression
  {q a : ℕ}
-- given
  (hq : q ≠ 0)
  (h : a.Coprime q) :
-- imply
  Set.Infinite {p : ℕ | p.Prime ∧ p ≡ a [MOD q]} :=
-- proof
  Nat.infinite_setOf_prime_and_modEq hq h
@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_infinite := infinite_primes_in_arithmeticProgression

end DirichletLFunction

namespace DirichletLFunction

/--
[frequently_prime_and_modEq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma frequently_prime_and_modEq
  {q a : ℕ}
-- given
  (hq : q ≠ 0)
  (h : a.Coprime q) :
-- imply
  ∃ᶠ p in atTop, p.Prime ∧ p ≡ a [MOD q] :=
-- proof
  Nat.frequently_atTop_prime_and_modEq hq h
@[deprecated (since := "2024-12-18")]
alias thm_18_1_dirichlet_frequently := frequently_prime_and_modEq

end DirichletLFunction

namespace DirichletLFunction

/--
[dirichletLSeries_changeLevel](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/DirichletL.lean)
-/
@[path]
lemma dirichletLSeries_changeLevel
  {M N : ℕ}
  [NeZero N]
  {χ : DirichletCharacter ℂ M}
  {s : ℂ}
-- given
  (hMN : M ∣ N)
  (hs : 1 < s.re) :
-- imply
  LSeries (↗(DirichletCharacter.changeLevel hMN χ)) s = LSeries ↗χ s * ∏ p ∈ N.primeFactors, (1 - χ p * (p : ℂ) ^ (-s)) :=
-- proof
  DirichletCharacter.LSeries_changeLevel hMN χ hs
@[deprecated (since := "2024-12-18")]
alias L_series_change_level := dirichletLSeries_changeLevel
end DirichletLFunction



-- created on 2026-10-23
