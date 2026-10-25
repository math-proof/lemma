import Mathlib.LinearAlgebra.Eigenspace.Triangularizable
import Mathlib.LinearAlgebra.Prod
import Mathlib.Topology.Algebra.OpenSubgroup
import Mathlib.Topology.Compactness.Compact
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

set_option autoImplicit false

namespace FLT.SmoothAdmissibleSchurCommutant

section FixedVectors

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

def fixedVectors (K : Subgroup G) : Submodule k V where
  carrier := {v : V | ∀ u ∈ K, π u v = v}
  add_mem' := by
    intro a b ha hb u hu
    rw [map_add, ha u hu, hb u hu]
  zero_mem' := by
    intro u hu
    rw [map_zero]
  smul_mem' := by
    intro c v hv u hu
    rw [map_smul, hv u hu]


def repStabilizer (v : V) : Subgroup G where
  carrier := {g : G | π g v = v}
  one_mem' := by
    simp only [Set.mem_setOf_eq, map_one, Module.End.one_apply]
  mul_mem' := by
    intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [map_mul, Module.End.mul_apply, hb, ha]
  inv_mem' := by
    intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    calc π a⁻¹ v = π a⁻¹ (π a v) := by rw [ha]
    _ = π (a⁻¹ * a) v := by rw [map_mul, Module.End.mul_apply]
    _ = v := by rw [inv_mul_cancel, map_one, Module.End.one_apply]

end FixedVectors

section Predicates

universe u v w

variable {k : Type u} [Field k] {G : Type v} [Group G]
variable {V : Type w} [AddCommGroup V] [Module k V]

variable (π : G →* Module.End k V)

def IsIrreducibleRep : Prop :=
  (∃ v : V, v ≠ 0) ∧
    ∀ W : Submodule k V,
      (∀ (g : G) (v : V), v ∈ W → π g v ∈ W) → W = ⊥ ∨ W = ⊤

variable [TopologicalSpace G]

def IsSmoothRep : Prop :=
  ∀ v : V, IsOpen ((repStabilizer π v : Subgroup G) : Set G)

def IsAdmissibleRep : Prop :=
  ∀ K : Subgroup G, IsCompact (K : Set G) → IsOpen (K : Set G) →
    FiniteDimensional k (fixedVectors π K)

end Predicates

end FLT.SmoothAdmissibleSchurCommutant
