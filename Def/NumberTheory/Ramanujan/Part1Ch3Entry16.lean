/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry16.lean -/

/-
Author: @akiezun, Avocado
-/

import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Def.NumberTheory.Ramanujan.Part1Ch3Entry12
import Lemma.Nat.Ramanujan.Part1Ch3Entry12
/-!
# Ramanujan's Notebooks, Part I, Chapter 3, Entry 16(a)

Recurrence relating varphi(r,n) to varphi(r+1,n) and varphi(r+1,n+1).
-/


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3

namespace Entry16

noncomputable def varphi (a x : ℂ) (s : ℤ) (m : ℂ) : ℂ :=
  Entry12.F s m a * Complex.exp (-m * Complex.log x)

end Entry16
end MathlibExt.NumberTheory.Ramanujan.Part1Ch3
