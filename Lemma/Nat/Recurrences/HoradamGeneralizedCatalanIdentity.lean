import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Recurrences.HoradamGeneralizedCatalanIdentity
open MetaMathlibExt


/--
[horadam_generalized_catalan_identity](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Recurrences/HoradamGeneralizedCatalanIdentity.lean)
-/
@[path]
private lemma horadam_generalized_catalan_identity_eq
  [CommRing R]
  {c₁ c₂ : R}
  {W Y U : ℕ → R}
  {s i j : ℕ}
-- given
  (hW : ∀ n, W (n + 2) = c₁ * W (n + 1) + c₂ * W n)
  (hY : ∀ n, Y (n + 2) = c₁ * Y (n + 1) + c₂ * Y n)
  (hU : ∀ n, U (n + 2) = c₁ * U (n + 1) + c₂ * U n)
  (hU0 : U 0 = 0)
  (hU1 : U 1 = 1) :
-- imply
  W (s + i) * Y (s + j) - W s * Y (s + i + j) =
    (-c₂) ^ s * (W 1 * Y j - W 0 * Y (j + 1)) * U i := by
-- proof
  apply MetaMathlibExt.horadam_generalized_catalan_identity c₁ c₂ W Y U hW hY hU hU0 hU1 s i j


-- created on 2026-10-20
