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

/--
Characters of finite-dimensional representations are class functions.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2.1 (the character is constant on conjugacy classes).
-/
theorem character_isClassFunction {G k : Type*} [Group G] [Field k]
    (V : FDRep k G) : IsClassFunction V.character :=
  fun g h => FDRep.char_conj V g h

private theorem classFunction_eq_of_isConj {G k : Type*} [Group G]
    {f : G → k} (hf : IsClassFunction f) {x y : G} (hxy : IsConj x y) : f x = f y := by
  obtain ⟨h, rfl⟩ := isConj_iff.mp hxy
  exact (hf x h).symm

/-- A class function takes equal values on conjugate elements. -/
theorem IsClassFunction.eq_of_isConj {G k : Type*} [Group G]
    {f : G → k} (hf : IsClassFunction f) {x y : G} (hxy : IsConj x y) : f x = f y :=
  classFunction_eq_of_isConj hf hxy

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

/-- Class functions are linearly equivalent to functions on conjugacy classes. -/
def classFunctionsEquivConjClasses (G : Type*) [Group G] (k : Type*) [Field k] :
    classFunctions G k ≃ₗ[k] (ConjClasses G → k) where
  toFun f := Quotient.lift f fun _ _ => f.property.eq_of_isConj
  invFun q :=
    ⟨q ∘ ConjClasses.mk,
      (isClassFunction_iff_factor_conjClasses _).2 ⟨q, fun _ => rfl⟩⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    rfl
  right_inv q := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_add' f g := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl
  map_smul' a f := by
    funext c
    refine Quotient.inductionOn c ?_
    intro x
    rfl

/-- Descending a class function and evaluating on its conjugacy class recovers its value. -/
@[simp]
theorem classFunctionsEquivConjClasses_apply_mk {G k : Type*} [Group G] [Field k]
    (f : classFunctions G k) (x : G) :
    classFunctionsEquivConjClasses G k f (ConjClasses.mk x) = (f : G → k) x :=
  rfl

/-- Lifting a function on conjugacy classes evaluates by the quotient map. -/
@[simp]
theorem classFunctionsEquivConjClasses_symm_apply {G k : Type*} [Group G] [Field k]
    (q : ConjClasses G → k) (x : G) :
    (↑((classFunctionsEquivConjClasses G k).symm q) : G → k) x = q (ConjClasses.mk x) :=
  rfl

/--
The space of class functions has dimension equal to the number of conjugacy
classes.

Sources: `undergrad.yaml`, section "Representation theory of finite groups",
entry "class function over a group"; J.-P. Serre, Linear Representations of
Finite Groups, GTM 42, §2.7, Theorem 6 (dimension count for class functions).

Proves `Wanted` entry `finrank_classFunctions_eq_card_conjClasses`.

Proof: Use `classFunctionsEquivConjClasses` and
`Module.finrank_fintype_fun_eq_card`, after obtaining a finite quotient from
`ConjClasses.mk_surjective`.
-/
theorem finrank_classFunctions_eq_card_conjClasses (G : Type*)
    [Group G] [Fintype G] (k : Type*) [Field k] :
    Module.finrank k ↥(classFunctions G k) = Nat.card (ConjClasses G) := by
  classical
  let _ : Fintype (ConjClasses G) :=
    Fintype.ofSurjective ConjClasses.mk ConjClasses.mk_surjective
  calc
    Module.finrank k ↥(classFunctions G k) = Module.finrank k (ConjClasses G → k) :=
      (classFunctionsEquivConjClasses G k).finrank_eq
    _ = Fintype.card (ConjClasses G) := Module.finrank_fintype_fun_eq_card k
    _ = Nat.card (ConjClasses G) := Fintype.card_eq_nat_card

end MathlibExt.GroupTheory.ClassFunctionWanted
