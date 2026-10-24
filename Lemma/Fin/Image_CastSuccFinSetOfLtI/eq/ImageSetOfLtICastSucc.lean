import Mathlib
import sympy.Basic


/--
[image_castSucc_eq_image](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/LieGroups/code/SyzygiesKoszul.lean)
-/
@[path]
private lemma main
  {k : ℕ}
  {f : Fin (k + 1) → α}
  {j : Fin k} :
-- imply
  Set.image (f ∘ Fin.castSucc) {i : Fin k | (i : ℕ) < (j : ℕ)} =
    Set.image f {i : Fin (k + 1) | (i : ℕ) < (Fin.castSucc j : ℕ)} := by
-- proof
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Function.comp]
  constructor
  ·
    rintro ⟨i, hi, rfl⟩
    exact ⟨Fin.castSucc i, by simp [Fin.castSucc, hi], rfl⟩
  ·
    rintro ⟨i, hi, rfl⟩
    have hik : (i : ℕ) < k := by
      have := j.isLt
      simp [Fin.castSucc] at hi
      omega
    exact ⟨⟨i, hik⟩, by simp [Fin.castSucc] at hi ⊢; exact hi, by simp [Fin.castSucc]⟩


-- created on 2026-10-24
