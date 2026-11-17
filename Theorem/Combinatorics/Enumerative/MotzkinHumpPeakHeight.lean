/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Enumerative/MotzkinHumpPeakHeight.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/
module

public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Fin.Basic
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Logic.Equiv.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Tactic
public import Def.Combinatorics.Enumerative.MotzkinHumpPeakHeight

public section

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
