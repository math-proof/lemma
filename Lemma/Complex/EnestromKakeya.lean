import Mathlib
import sympy.Basic
import sympy.Analysis.Complex.EnestromKakeya

open Complex.EnestromKakeya

/--
[enestrom_kakeya_zero_localization](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Complex/EnestromKakeya.lean)
-/
@[path]
private lemma enestrom_kakeya_zero_localization_eq
-- given
  {n : ℕ} (a : Fin (n + 1) → ℝ) (hn : 1 ≤ n) (hpos : ∀ k, 0 < a k) :
-- imply
  ∀ z : ℂ,
    (∑ k : Fin (n + 1),
      Polynomial.C ((a k : ℝ) : ℂ) * Polynomial.X ^ (k : ℕ)).IsRoot z →
      (Finset.image (fun k : Fin n => a k.castSucc / a k.succ) Finset.univ).min'
        ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn⟩)⟩ ≤ ‖z‖ ∧
      ‖z‖ ≤ (Finset.image (fun k : Fin n => a k.castSucc / a k.succ)
        Finset.univ).max'
        ⟨_, Finset.mem_image_of_mem _ (Finset.mem_univ ⟨0, hn⟩)⟩ := by
-- proof
  apply enestrom_kakeya_zero_localization hn a hpos


-- created on 2026-10-09
