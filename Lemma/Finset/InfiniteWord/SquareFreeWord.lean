import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.InfiniteWord.SquareFreeWord
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isSquareFreeWord_iff_inits_tails](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SquareFreeWord.lean)
-/
@[path]
lemma isSquareFreeWord_iff_inits_tails
  {w : List α} :
-- imply
  IsSquareFreeWord w ↔
    ∀ s ∈ w.tails.flatMap List.inits, ∀ x ∈ s.inits, x ≠ [] → s ≠ x ++ x := by
-- proof
  constructor
  · intro hw s hs x _ hx heq
    rw [List.mem_flatMap] at hs
    obtain ⟨t, ht, hs⟩ := hs
    have hsw : s.IsInfix w := ((List.mem_inits s t).mp hs).isInfix.trans
      ((List.mem_tails t w).mp ht).isInfix
    exact hw s hsw ⟨x, hx, heq⟩
  · intro h s hs ⟨x, hx, heq⟩
    rw [List.infix_iff_prefix_suffix] at hs
    obtain ⟨t, hst, htw⟩ := hs
    have hsmem : s ∈ w.tails.flatMap List.inits := by
      rw [List.mem_flatMap]
      exact ⟨t, (List.mem_tails t w).mpr htw, (List.mem_inits s t).mpr hst⟩
    exact h s hsmem x ((List.mem_inits x s).mpr ⟨x, heq.symm⟩) hx heq

end MetaMathlibExt

/--
[IsSquareFreeWord.of_isInfix](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/InfiniteWord/SquareFreeWord.lean)
-/
@[path]
lemma IsSquareFreeWord.of_isInfix
  {u v : List α}
-- given
  (hv : IsSquareFreeWord v)
  (huv : u.IsInfix v) :
-- imply
  IsSquareFreeWord u := by
-- proof
  intro s hs
  exact hv s (hs.trans huv)



-- created on 2026-10-20
-- updated on 2026-10-23
