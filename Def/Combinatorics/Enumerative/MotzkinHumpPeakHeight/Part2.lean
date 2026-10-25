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
import Theorem.Combinatorics.Enumerative.MotzkinHumpPeakHeight


namespace MetaMathlibExt

open scoped BigOperators

/-- Prefix part of a shaped path. -/
def mhShapeFst {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin i.val) : Fin 3 :=
  p ⟨r.val, by
    have _hs := r.is_lt
    have _hi := i.is_lt
    omega⟩

/-- Suffix part of a shaped path. -/
def mhShapeSnd {n : ℕ} {i j : Fin n} (_hij : i.val < j.val)
    (p : Fin n → Fin 3) (r : Fin (n - 1 - j.val)) : Fin 3 :=
  p ⟨j.val + 1 + r.val, by
    have _hs := r.is_lt
    have _hj := j.is_lt
    omega⟩

def mhShapeEquiv {n : ℕ} {i j : Fin n} (hij : i.val < j.val) :
    {p : Fin n → Fin 3 // mhIsShape p i j} ≃
      (Fin i.val → Fin 3) × (Fin (n - 1 - j.val) → Fin 3) where
  toFun := fun q => (fun s => mhShapeFst hij q.1 s, fun s => mhShapeSnd hij q.1 s)
  invFun := fun q => ⟨mhGlue hij q.1 q.2,
    mhGlue_eq_i hij q.1 q.2 rfl,
    fun r hr1 hr2 => mhGlue_of_between hij q.1 q.2 hr1 hr2,
    mhGlue_eq_j hij q.1 q.2 rfl⟩
  left_inv := by
    intro pp
    obtain ⟨p, h1, h2, h3⟩ := pp
    apply Subtype.ext
    change mhGlue hij (fun s => mhShapeFst hij p s)
        (fun s => mhShapeSnd hij p s) = p
    apply funext
    intro r
    by_cases hr1 : r.val < i.val
    · rw [mhGlue_of_lt hij _ _ hr1]
      unfold mhShapeFst
      congr 1
    · by_cases hr2 : r.val = i.val
      · have hri : r = i := Fin.ext hr2
        subst hri
        rw [mhGlue_eq_i hij _ _ rfl]
        exact h1.symm
      · by_cases hr3 : r.val < j.val
        · have hbt : i.val < r.val := by omega
          rw [mhGlue_of_between hij _ _ hbt hr3]
          exact (h2 r hbt hr3).symm
        · by_cases hr4 : r.val = j.val
          · have hrj : r = j := Fin.ext hr4
            subst hrj
            rw [mhGlue_eq_j hij _ _ rfl]
            exact h3.symm
          · have hlt : j.val < r.val := by omega
            rw [mhGlue_of_after hij _ _ hlt]
            change mhShapeSnd hij p ⟨r.val - j.val - 1, _⟩ = p r
            unfold mhShapeSnd
            congr 1
            apply Fin.ext
            change j.val + 1 + (r.val - j.val - 1) = r.val
            have _hrn := r.is_lt
            have _hj := j.is_lt
            omega
  right_inv := by
    intro q
    obtain ⟨α, β⟩ := q
    change (fun s => mhShapeFst hij (mhGlue hij α β) s,
      fun s => mhShapeSnd hij (mhGlue hij α β) s) = (α, β)
    apply Prod.ext
    · apply funext
      intro s
      change mhGlue hij α β ⟨s.val, _⟩ = α s
      rw [mhGlue_of_lt hij α β (by have _hs := s.is_lt; omega)]
    · apply funext
      intro s
      change mhGlue hij α β ⟨j.val + 1 + s.val, _⟩ = β s
      have hlt : j.val < j.val + 1 + s.val := by omega
      rw [mhGlue_of_after hij α β hlt]
      congr 1
      apply Fin.ext
      change j.val + 1 + s.val - j.val - 1 = s.val
      have _hs := s.is_lt
      have _hj := j.is_lt
      omega

end MetaMathlibExt
