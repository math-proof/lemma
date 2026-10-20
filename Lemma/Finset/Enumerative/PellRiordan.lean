import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Enumerative.PellRiordan
open MetaMathlibExt


/--
[pell_riordan_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellRiordan.lean)
-/
@[path]
private lemma pell_riordan_general_eq
  :
-- imply
  (k : ℕ) (p : ℕ → ℕ → ℕ)
    (hgen : ∀ n : ℕ,
    PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := by
-- proof
  apply MetaMathlibExt.pell_riordan_general

/--
[pell_riordan](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/PellRiordan.lean)
-/
@[path]
private lemma pell_riordan_eq
  :
-- imply
  ∀ (k : ℕ) (hk : 2 ≤ k) (p : ℕ → ℕ → ℕ)
    (hgen : ∀ n : ℕ,
    PowerSeries.mk (fun m => (↑(p n m) : ℚ)) * (1 - PowerSeries.X (R := by
-- proof
  apply MetaMathlibExt.pell_riordan


-- created on 2026-10-20
