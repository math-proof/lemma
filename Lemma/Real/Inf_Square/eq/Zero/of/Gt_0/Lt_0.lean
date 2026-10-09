import sympy.sets.sets
import sympy.Basic
import Mathlib.Data.Real.Basic


@[path]
private lemma main
  {m M : ℝ}
-- given
  (hM : M > 0)
  (hm : m < 0) :
-- imply
  sInf ((fun x => x ^ 2) '' Set.Ioo m M) = 0 := by
-- proof
  have hlb : 0 ∈ lowerBounds ((fun x => x ^ 2) '' Set.Ioo m M) := by
    rintro z ⟨x, ⟨hx1, hx2⟩, rfl⟩
    exact sq_nonneg x
  have hmem : (0:ℝ) ∈ (fun x => x ^ 2) '' Set.Ioo m M :=
    ⟨0, ⟨by linarith, by linarith⟩, by norm_num⟩
  exact le_antisymm (csInf_le ⟨0, hlb⟩ hmem) (le_csInf ⟨0, hmem⟩ hlb)


-- created on 2019-08-24
