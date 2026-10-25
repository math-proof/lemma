/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/Partition/PeakGeneratingFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Polynomial.Chebyshev
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Abbrev.Combinatorics.Enumerative.Partition.PeakGeneratingFunction


namespace MetaMathlibExt

noncomputable def pgf_x : pgfR := PowerSeries.X

noncomputable def pgf_q : pgfR := PowerSeries.C Polynomial.X

noncomputable def pgf_y : pgfR := pgf_x ^ 2 * (1 - pgf_q)

noncomputable def pgf_G : ℕ → pgfR
  | 0 => 1
  | 1 => 1
  | n + 2 => (2 + pgf_y) * pgf_G (n + 1) - pgf_G n

noncomputable def pgf_map (f : pgfR) : pgfK :=
  algebraMap pgfR pgfK f

noncomputable def pgf_t : pgfK :=
  1 + pgf_map pgf_x ^ 2 * (1 - pgf_map pgf_q) / 2

noncomputable def pgf_U (m : ℤ) : pgfK :=
  (Polynomial.Chebyshev.U pgfK m).eval pgf_t

noncomputable def pgf_A : pgfR := pgf_x * (pgf_q - 1)

noncomputable def pgf_B : pgfR := 1 - pgf_x * (pgf_q - 1)

noncomputable def pgf_C : pgfR :=
  1 - pgf_x * (1 - pgf_q) * (1 - pgf_x)

noncomputable def pgf_D : pgfR :=
  -pgf_x * (pgf_x + pgf_q * (1 - pgf_x))

def pgf_isPeakAt {n m : ℕ} (w : Fin n → Fin m) (i : Fin n) : Prop :=
  i.val ≠ 0 ∧
    if h : i.val + 1 < n then
      w ⟨i.val - 1, lt_of_le_of_lt (Nat.sub_le i.val 1) i.isLt⟩ < w i ∧
        w ⟨i.val + 1, h⟩ < w i
    else False

end MetaMathlibExt
