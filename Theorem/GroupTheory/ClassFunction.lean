/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.Conj
import Def.GroupTheory.ClassFunction


namespace MathlibExt.GroupTheory.ClassFunctionWanted

/--
A function is a class function iff it factors through the quotient onto
conjugacy classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2 (class functions as functions on conjugacy classes).

Proves `Wanted` entry `isClassFunction_iff_factor_conjClasses`.

Proof: Descend a class function with `Quotient.lift`, using `isConj_iff` for
well-definedness, and use equality in `ConjClasses` for the converse.
-/
theorem isClassFunction_iff_factor_conjClasses {G k : Type*}
    [Group G] (f : G → k) :
    IsClassFunction f ↔ ∃ g : ConjClasses G → k, ∀ x : G, f x = g (ConjClasses.mk x) := by
  constructor
  · intro hf
    exact ⟨Quotient.lift f fun _ _ => hf.eq_of_isConj, fun _ => rfl⟩
  · rintro ⟨q, hq⟩ x h
    calc
      f (h * x * h⁻¹) = q (ConjClasses.mk (h * x * h⁻¹)) := hq _
      _ = q (ConjClasses.mk x) := by
        apply congrArg q
        exact
          (ConjClasses.mk_eq_mk_iff_isConj.2 (isConj_iff.2 ⟨h, rfl⟩)).symm
      _ = f x := (hq x).symm

end MathlibExt.GroupTheory.ClassFunctionWanted
