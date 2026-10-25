/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/ClassFunction.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.RepresentationTheory.Character
import Mathlib.Algebra.Group.Conj


namespace MathlibExt.GroupTheory.ClassFunctionWanted

/-!
# Class functions on groups

A class function is constant on conjugacy classes. Characters of
finite-dimensional representations are the motivating examples; the space of
class functions has dimension equal to the number of conjugacy classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group" (reference-only, no Lean formalization);
J.-P. Serre, Linear Representations of Finite Groups, GTM 42, §2 (functions on
a group, class functions).
-/

/-- A function is a class function when it is constant on conjugacy classes. -/
def IsClassFunction {G k : Type*} [Group G] (f : G → k) : Prop :=
  ∀ g h : G, f (h * g * h⁻¹) = f g

/-- Class functions as a submodule of all functions. -/
def classFunctions (G : Type*) [Group G] (k : Type*) [Field k] :
    Submodule k (G → k) where
  carrier := {f | IsClassFunction f}
  zero_mem' := fun _ _ => rfl
  add_mem' := fun hf hg a b => by simp only [Pi.add_apply, hf a b, hg a b]
  smul_mem' := fun c f hf a b => by simp only [Pi.smul_apply, hf a b]

end MathlibExt.GroupTheory.ClassFunctionWanted
