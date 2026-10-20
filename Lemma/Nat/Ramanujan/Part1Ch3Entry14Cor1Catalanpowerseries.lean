import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry14Cor1Catalanpowerseries
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry14Cor1Catalanpowerseries


/--
[ramanujan_part1_ch3_entry14_cor1_catalanpowerseries](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry14Cor1Catalanpowerseries.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry14_cor1_catalanpowerseries_eq
  {n a : ℝ}
-- given
  (ha : |a| ≤ 1 / 4) :
-- imply
  let term := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry14Cor1Catalanpowerseries.ramanujan_part1_ch3_entry14_cor1_catalanpowerseries n a ha


-- created on 2026-10-20
