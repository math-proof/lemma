module

public import Mathlib
public import Instance.Deformations_ContinuousSMulDiscrete
public import Instance.RepTheory_SmoothVectors
public import Def.FLTPrelim_RightTranslationFn

@[expose] public section

set_option autoImplicit false

open scoped Topology

namespace FLT.SmoothVectors

section Predicate

variable {G : Type*} [Group G] [TopologicalSpace G]
variable {M : Type*}

def IsSmoothVector (G : Type*) {M : Type*} [Group G] [TopologicalSpace G] [MulAction G M]
    (v : M) : Prop :=
  IsOpen ((MulAction.stabilizer G v : Subgroup G) : Set G)

variable [MulAction G M]

end Predicate


section Submodule

variable (G : Type*) [Group G] [TopologicalSpace G] [ContinuousMul G]
variable (R : Type*) [Semiring R]
variable (M : Type*) [AddCommMonoid M] [Module R M]
variable [DistribMulAction G M] [SMulCommClass G R M]

def smoothVectors : Submodule R M where
  carrier := {v : M | IsSmoothVector G v}
  zero_mem' := isSmoothVector_zero
  add_mem' hv hw := hv.add hw
  smul_mem' r _v hv := hv.const_smul r

variable {G R M}

end Submodule


end FLT.SmoothVectors
