import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.NumberTheory.Ramanujan.Part1Ch3Entry3
open MathlibExt.NumberTheory.Ramanujan.Part1Ch3
open Entry3


namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

/--
[fCoeff_eq_generalizedBellGenerating](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
lemma fCoeff_eq_generalizedBellGenerating
  {x : ℂ}
  {j : ℕ} :
-- imply
  fCoeff x j =
    Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x j := by
-- proof
  unfold fCoeff
    Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating
  congr 1
  apply tsum_congr
  intro k
  simp only [zero_add, one_mul]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

/--
[prod_entry9_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
private lemma prod_entry9_eq (z : ℂ) (j : ℕ) :
  (∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)))
    = ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) := by
  apply Finset.prod_congr rfl
  intro r _
  have hcast : (((r + 1 : ℕ)) : ℂ) = (r : ℂ) + 1 := by push_cast; ring
  rw [hcast]
  ring

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

/--
[psi_eq_entry9_P](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
lemma psi_eq_entry9_P
  {x z : ℂ} :
-- imply
  psi x z = Entry9Odd.entry9_P 0 1 x z := by
-- proof
  unfold psi Entry9Odd.entry9_P
  apply tsum_congr
  intro j
  have hprod := prod_entry9_eq z j
  by_cases h : ∏ i ∈ Finset.range (j + 1), (z + ((i + 1 : ℕ) : ℂ)) = 0
  · have h2 : ∏ r ∈ Finset.range (j + 1), (z + (0 : ℂ) + (1 : ℂ) * ((r : ℂ) + 1)) = 0 :=
    hprod.trans h
    rw [ite_eq_left h, h2]
    simp
  · rw [ite_eq_right h, ← hprod]

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

/--
[ramanujan_part1_ch3_entry3_general](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry3_general
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
  have h9 :=
    Entry9Odd.ramanujan_part1_ch3_entry9_odd (a := 0) (b := 1) (x := x) (ε := ε) (n := N)
      one_ne_zero hε_pos hε_lt
  have hfun : (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ)) = id := by
    funext z
    simp
  have hfilter :
    Filter.comap (fun z : ℂ => (z + (0 : ℂ)) / (1 : ℂ))
      (Filter.cocompact ℂ ⊓ Filter.principal
        {w : ℂ | -Real.pi + ε ≤ Complex.arg w ∧ Complex.arg w ≤ Real.pi - ε})
      = Filter.cocompact ℂ ⊓ Filter.principal (sector ε) := by
    rw [hfun, Filter.comap_id]
    rfl
  rw [hfilter] at h9
  have hsum : ∀ z : ℂ, (Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
    ((-1 : ℂ) ^ k *
      Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
      / z ^ (k + 1)))
    = ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)) := by
    intro z
    apply Finset.sum_congr rfl
    intro j _
    simp only [fCoeff_eq_generalizedBellGenerating]
  have hLHS :
    (fun z : ℂ => psi x z -
      ∑ j ∈ Finset.range (N + 1), ((-1 : ℂ) ^ j * fCoeff x j / z ^ (j + 1)))
    = fun z : ℂ => -((Finset.sum (Finset.range (N + 1)) (fun k : ℕ =>
      ((-1 : ℂ) ^ k *
        Entry9IiGeneralizedbellgeneratingDefining.generalizedBellGenerating 0 1 x k)
        / z ^ (k + 1)) - Entry9Odd.entry9_P 0 1 x z)) := by
    funext z
    rw [← psi_eq_entry9_P, hsum z]
    ring
  rw [hLHS]
  exact h9.neg_left

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

namespace MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3

/--
[ramanujan_part1_ch3_entry3](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/NumberTheory/Ramanujan/Part1Ch3Entry3.lean)
-/
@[path]
lemma ramanujan_part1_ch3_entry3
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
  have _ : x ≠ 0 := hx
  exact ramanujan_part1_ch3_entry3_general (x := x) (ε := ε) (N := N) hε_pos hε_lt

end MathlibExt.NumberTheory.Ramanujan.Part1Ch3.Entry3


-- created on 2026-10-20
-- updated on 2026-10-29
