import Mathlib
import sympy.Basic
import sympy.atlas.NumberTheory.Ramanujan.Part1Ch3Entry3
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry3


/--
[fCoeff_eq_generalizedBellGenerating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
private lemma fCoeff_eq_generalizedBellGenerating_eq
  {x : ℂ}
  {j : ℕ} :
-- imply
  fCoeff x j =
    Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x j := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3.fCoeff_eq_generalizedBellGenerating x j

/--
[psi_eq_entry9_P](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
private lemma psi_eq_entry9_P_eq
  {x z : ℂ} :
-- imply
  psi x z = Entry9Odd.entry9_P 0 1 x z := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3.psi_eq_entry9_P x z

/--
[ramanujan_part1_ch3_entry3_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry3_general_eq
  {x : ℂ}
  {ε : ℝ}
  {N : ℕ}
-- given
  (hε_pos : 0 < ε)
  (hε_lt : ε < Real.pi) :
-- imply
  Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
    (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
    (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3.ramanujan_part1_ch3_entry3_general x ε hε_pos hε_lt N

/--
[ramanujan_part1_ch3_entry3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
private lemma ramanujan_part1_ch3_entry3_eq
  {x : ℂ}
  {ε : ℝ}
  {N : ℕ}
-- given
  (hx : x ≠ 0)
  (hε_pos : 0 < ε)
  (hε_lt : ε < Real.pi) :
-- imply
  Asymptotics.IsBigO (Filter.cocompact ℂ ⊓ Filter.principal (sector ε))
    (fun z : ℂ => psi x z - ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
    (fun z : ℂ => (1 : ℂ) / z ^ (N + 2)) := by
-- proof
  apply MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3.ramanujan_part1_ch3_entry3 x hx ε hε_pos hε_lt N


-- created on 2026-10-20
