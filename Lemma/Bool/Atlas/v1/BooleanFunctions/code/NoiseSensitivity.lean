import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.BooleanFunctions.code.NoiseSensitivity
open Finset BigOperators BooleanFourier


namespace BooleanFourier

/--
[parseval_boolToReal](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseSensitivity.lean)
-/
@[path]
lemma parseval_boolToReal
  {n : ℕ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  ∑ S : Finset (Fin n), fourierCoeff (fun x => boolToReal (f x)) S ^ 2 = 1 := by
-- proof
  have hpars := parseval (fun x => boolToReal (f x))
  rw [hpars]
  have hval : ∀ x : Fin n → Bool, (boolToReal (f x)) ^ 2 = 1 :=
    fun x => boolToReal_sq (f x)
  simp_rw [hval]
  simp [Fintype.card_bool, Fintype.card_fin]

end BooleanFourier

namespace BooleanFourier

/--
[noiseSensitivity_eq_fourier_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/BooleanFunctions/code/NoiseSensitivity.lean)
-/
@[path]
lemma noiseSensitivity_eq_fourier_sum
  {n : ℕ}
  {δ : ℝ}
  {f : (Fin n → Bool) → Bool} :
-- imply
  noiseSensitivity δ f = 1 / 2 * ∑ S : Finset (Fin n), (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff (fun x => boolToReal (f x)) S ^ 2 := by
-- proof
  set g : (Fin n → Bool) → ℝ := fun x => boolToReal (f x) with hg_def
  have hstab : noiseStability (1 - 2 * δ) g =
    ∑ S : Finset (Fin n), (1 - 2 * δ) ^ S.card * fourierCoeff g S ^ 2 :=
    noiseStability_eq_sum (1 - 2 * δ) g
  have hpars : ∑ S : Finset (Fin n), fourierCoeff g S ^ 2 = 1 :=
    parseval_boolToReal f
  calc noiseSensitivity δ f
    = (1 - noiseStability (1 - 2 * δ) g) / 2 := by
      rfl
    _ = (1 - ∑ S : Finset (Fin n),
      (1 - 2 * δ) ^ S.card * fourierCoeff g S ^ 2) / 2 := by
      rw [hstab]
    _ = (∑ S : Finset (Fin n), fourierCoeff g S ^ 2 -
      ∑ S : Finset (Fin n),
        (1 - 2 * δ) ^ S.card * fourierCoeff g S ^ 2) / 2 := by
      rw [← hpars]
    _ = 1 / 2 * (∑ S : Finset (Fin n), fourierCoeff g S ^ 2 -
      ∑ S : Finset (Fin n),
        (1 - 2 * δ) ^ S.card * fourierCoeff g S ^ 2) := by
      ring
    _ = 1 / 2 * ∑ S : Finset (Fin n),
      (fourierCoeff g S ^ 2 -
        (1 - 2 * δ) ^ S.card * fourierCoeff g S ^ 2) := by
      congr 1
      rw [← Finset.sum_sub_distrib]
    _ = 1 / 2 * ∑ S : Finset (Fin n),
      (1 - (1 - 2 * δ) ^ S.card) * fourierCoeff g S ^ 2 := by
      congr 1
      exact Finset.sum_congr rfl (fun S _ => by ring)

end BooleanFourier


-- created on 2026-10-23
