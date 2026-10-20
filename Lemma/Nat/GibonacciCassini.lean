import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.GibonacciCassini
open MetaMathlibExt


/--
[gibonacci_cassini_of_pos](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/GibonacciCassini.lean)
-/
@[path]
private lemma gibonacci_cassini_of_pos_eq
  {G₀ G₁ : ℤ}
  {n : ℕ}
-- given
  (hn : 1 ≤ n) :
-- imply
  gibonacciNumber G₀ G₁ (n + 1) * gibonacciNumber G₀ G₁ (n - 1) -
    (gibonacciNumber G₀ G₁ n) ^ 2 =
    (-1 : ℤ) ^ n * (G₁ ^ 2 - G₀ * G₁ - G₀ ^ 2) := by
-- proof
  apply MetaMathlibExt.gibonacci_cassini_of_pos G₀ G₁ n hn


-- created on 2026-10-20
