import Mathlib
import sympy.Basic
import Def.Combinatorics.VanDerLaanSequence
open MetaMathlibExt


namespace MetaMathlibExt

/--
[isVanDerLaanWindow_ordered_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
lemma isVanDerLaanWindow_ordered_iff
  {a b c d : ℕ}
-- given
  (hab : a ≤ b)
  (hbc : b ≤ c)
  (hcd : c ≤ d) :
-- imply
  IsVanDerLaanWindow a b c d ↔ d = a + b := by
-- proof
  have hmax : max (max a b) (max c d) = d := by omega
  have hmin : min (min (a + b) (a + c)) (min (min (a + d) (b + c)) (min (b + d) (c + d)))
    = a + b := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isVanDerLaanWindow_const_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
lemma isVanDerLaanWindow_const_iff
  {k : ℕ} :
-- imply
  IsVanDerLaanWindow k k k k ↔ k = 0 := by
-- proof
  have hmax : max (max k k) (max k k) = k := by omega
  have hmin : min (min (k + k) (k + k)) (min (min (k + k) (k + k)) (min (k + k) (k + k)))
    = k + k := by omega
  unfold IsVanDerLaanWindow
  rw [hmax, hmin]
  constructor <;> intro h <;> omega

end MetaMathlibExt

namespace MetaMathlibExt

/--
[isVanDerLaan_const_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/VanDerLaanSequence.lean)
-/
@[path]
lemma isVanDerLaan_const_iff
  {k : ℕ} :
-- imply
  IsVanDerLaan (fun _ => k) ↔ k = 0 := by
-- proof
  constructor
  · intro h
    have h0 : IsVanDerLaanWindow k k k k := h 0
    exact isVanDerLaanWindow_const_iff.mp h0
  · intro hk n
    subst hk
    change IsVanDerLaanWindow 0 0 0 0
    unfold IsVanDerLaanWindow
    decide

end MetaMathlibExt


-- created on 2026-10-20
-- updated on 2026-10-23
