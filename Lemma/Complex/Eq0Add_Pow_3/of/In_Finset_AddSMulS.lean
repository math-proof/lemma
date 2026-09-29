import sympy.functions.elementary.complexes
import sympy.Basic
import sympy.polys.cardano
open Real


@[main]
private lemma sub.given
  {x p q δ : ℂ}
  {d : ℤ}
-- given
  (hδ : δ = 4 * p ^ 3 / 27 + q ^ 2)
  (h₀ : ⌈3 * arg (-p / 3) / (π * 2) - 1 / 2⌉ - (if p * (⌈(arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q)) / (2 * π) - 1 / 2⌉ : ℂ) = 0 then 0 else if arg (δ ^ (1 / 2 : ℂ) - q) + arg (-δ ^ (1 / 2 : ℂ) - q) > π then 1 else -1) = d)
  (h₁ : x = (δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d + (-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ)) :
-- imply
  x ^ 3 + p * x + q = 0 := by
-- proof
  have hK := Cardano.key hδ h₀
  have hW3 := Cardano.zpow_cube (d := d)
  have hsum := Cardano.cube_add (q := q) (δ := δ)
  rw [h₁]
  linear_combination (3 * ((δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ) * (-1 / 2 + Complex.I * √3 / 2) ^ d + (-δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ))) * hK + ((δ ^ (1 / 2 : ℂ) / 2 - q / 2) ^ (1 / 3 : ℂ)) ^ 3 * hW3 + hsum


-- created on 2026-09-27
