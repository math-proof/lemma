/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/SimpleGraph/Frucht.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.GroupTheory.Perm.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Order.Interval.Finset.Fin

@[expose] public section

namespace SimpleGraph

/-- Composition of graph automorphisms, matching permutation order:
`(a * b) x = a (b x)`. -/
instance {V : Type*} {G : SimpleGraph V} : Mul (G ≃g G) := ⟨fun a b => b.trans a⟩

/-- Identity automorphism. -/
instance {V : Type*} {G : SimpleGraph V} : One (G ≃g G) := ⟨RelIso.refl _⟩

/-- Inverse automorphism. -/
instance {V : Type*} {G : SimpleGraph V} : Inv (G ≃g G) := ⟨fun a => a.symm⟩

/-- Automorphisms of a graph form a group under composition. -/
instance instGroupIsoSelf {V : Type*} {G : SimpleGraph V} : Group (G ≃g G) where
  mul_assoc a b c := RelIso.ext fun x => rfl
  one_mul a := RelIso.ext fun x => rfl
  mul_one a := RelIso.ext fun x => rfl
  inv_mul_cancel a := RelIso.ext fun x => RelIso.symm_apply_apply a x

end SimpleGraph
