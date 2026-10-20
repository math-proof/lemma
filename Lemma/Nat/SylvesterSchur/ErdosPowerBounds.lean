import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.SylvesterSchur.ErdosPowerBounds
open scoped BigOperators
open Finset Nat
open Nat.SylvesterSchur


/--
[central_erdos_layers_two_mul_add_two_lt_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma central_erdos_layers_two_mul_add_two_lt_four_pow_eq
  {n : ℕ}
-- given
  (hn : 512 ≤ n) :
-- imply
  n * (∏ j ∈ Finset.range (Nat.log 2 (2 * n + 2)),
    if j = 0 then primorial ((2 * n + 2) / 3)
    else primorial (Nat.nthRoot (j + 1) (2 * n + 2))) < 4 ^ n := by
-- proof
  apply Nat.SylvesterSchur.central_erdos_layers_two_mul_add_two_lt_four_pow hn

/--
[erdos_layers_le_four_pow](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_eq
  {N r : ℕ} :
-- imply
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N * Nat.log 2 N) := by
-- proof
  apply Nat.SylvesterSchur.erdos_layers_le_four_pow N r

/--
[erdos_layers_le_four_pow_three_layers](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/SylvesterSchur/ErdosPowerBounds.lean)
-/
@[path]
private lemma erdos_layers_le_four_pow_three_layers_eq
  {N r : ℕ} :
-- imply
  (∏ j ∈ Finset.range (Nat.log 2 N),
    if j = 0 then primorial r else primorial (Nat.nthRoot (j + 1) N)) ≤
    4 ^ (r + Nat.sqrt N + Nat.nthRoot 3 N * Nat.log 2 N) := by
-- proof
  apply Nat.SylvesterSchur.erdos_layers_le_four_pow_three_layers N r


-- created on 2026-10-20
