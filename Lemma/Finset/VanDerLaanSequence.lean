import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.VanDerLaanSequence
open MetaMathlibExt


/--
[isVanDerLaanWindow_ordered_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
private lemma isVanDerLaanWindow_ordered_iff_eq
  {a b c d : ℕ}
-- given
  (hab : a ≤ b)
  (hbc : b ≤ c)
  (hcd : c ≤ d) :
-- imply
  IsVanDerLaanWindow a b c d ↔ d = a + b := by
-- proof
  apply MetaMathlibExt.isVanDerLaanWindow_ordered_iff hab hbc hcd

/--
[isVanDerLaanWindow_const_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
private lemma isVanDerLaanWindow_const_iff_eq
  {k : ℕ} :
-- imply
  IsVanDerLaanWindow k k k k ↔ k = 0 := by
-- proof
  apply MetaMathlibExt.isVanDerLaanWindow_const_iff

/--
[isVanDerLaan_const_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
private lemma isVanDerLaan_const_iff_eq
  {k : ℕ} :
-- imply
  IsVanDerLaan (fun _ => k) ↔ k = 0 := by
-- proof
  apply MetaMathlibExt.isVanDerLaan_const_iff


-- created on 2026-10-20
