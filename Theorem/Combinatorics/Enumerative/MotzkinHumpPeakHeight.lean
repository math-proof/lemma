/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinHumpPeakHeight.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Sigma
import Mathlib.Logic.Equiv.Basic
import Mathlib.Logic.Equiv.Prod
import Mathlib.SetTheory.Cardinal.Finite
import Mathlib.Tactic
import Def.Combinatorics.Enumerative.MotzkinHumpPeakHeight


namespace MetaMathlibExt

open scoped BigOperators

theorem mhGlue_of_lt {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val < i.val) :
    mhGlue _hij α β r = α ⟨r.val, hr⟩ := by
  unfold mhGlue
  rw [dite_eq_left hr]

theorem mhGlue_eq_i {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = i.val) :
    mhGlue _hij α β r = 2 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val), dite_eq_left hr]

theorem mhGlue_of_between {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr1 : i.val < r.val) (hr2 : r.val < j.val) :
    mhGlue _hij α β r = 1 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val), dite_eq_left hr2]

theorem mhGlue_eq_j {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : r.val = j.val) :
    mhGlue _hij α β r = 0 := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val), dite_eq_left hr]

theorem mhGlue_of_after {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (α : Fin i.val → Fin 3) (β : Fin (n - 1 - j.val) → Fin 3)
    {r : Fin n} (hr : j.val < r.val) :
    mhGlue _hij α β r =
      β ⟨r.val - j.val - 1, by
        have _hrn := r.is_lt
        have _hj := j.is_lt
        omega⟩ := by
  unfold mhGlue
  rw [dite_eq_right (by omega : ¬ r.val < i.val),
    dite_eq_right (by omega : ¬ r.val = i.val),
    dite_eq_right (by omega : ¬ r.val < j.val),
    dite_eq_right (by omega : ¬ r.val = j.val)]

end MetaMathlibExt
