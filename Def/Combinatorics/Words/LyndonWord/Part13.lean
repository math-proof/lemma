/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/LyndonWord.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Def.Algebra.Lie.WittMultigradedValue
import Def.Combinatorics.Words.PrimitiveWord
import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Vector
import Mathlib.Data.List.Lex
import Mathlib.Data.List.PeriodicityLemma
import Abbrev.Combinatorics.Words.LyndonWord.Part2
open scoped BigOperators

/-!
# Lyndon words

This file defines finite Lyndon words and word content, and counts Lyndon words with prescribed
content using Witt's multigraded value.
-/


namespace MetaMathlibExt

noncomputable def wittWordToRootData {r : ℕ} (degree : Fin r → ℕ)
    (hdegree : 0 < ∑ i, degree i) (w : WordsOfContent degree) :
    WittPrimitiveRootData degree :=
  let hw := wittWord_ne_nil w hdegree
  let d := wittExponent w.1 hw
  ⟨⟨d, Nat.mem_divisors.mpr
      ⟨wittExponent_dvd_gcd w hdegree, wittGcd_ne_zero degree hdegree⟩⟩,
    ⟨⟨wittRoot w.1 hw, wittRoot_content w hdegree⟩, wittRoot_isPrimitive w.1 hw⟩⟩

def wittRootDataToWord {r : ℕ} (degree : Fin r → ℕ)
    (p : WittPrimitiveRootData degree) : WordsOfContent degree :=
  ⟨wittWordPower p.2.1.1 p.1.1, by
    rw [wittWordContent_power, p.2.1.2]
    funext i
    have hdg : p.1.1 ∣ Finset.univ.gcd degree := (Nat.mem_divisors.mp p.1.2).1
    have hgd : Finset.univ.gcd degree ∣ degree i := Finset.gcd_dvd (Finset.mem_univ i)
    exact Nat.mul_div_cancel' (hdg.trans hgd)⟩

end MetaMathlibExt
