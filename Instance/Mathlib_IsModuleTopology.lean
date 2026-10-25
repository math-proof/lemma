-- Carved from Lemma/Definitions/Def_Mathlib_IsModuleTopology.lean: instance decls only.
import Mathlib
import Class.Mathlib_IsModuleTopology

section IsTopologicalModuleDep

open Topology

variable (R : Type*) [Ring R] [TopologicalSpace R]

variable [IsTopologicalModule R M]

instance Submodule.instIsTopologicalModuleSubtypeMem (S : Submodule R M) : IsTopologicalModule R S
    := IsInducing.subtypeVal.topologicalModule R S.subtypeL

instance Pi.instTopologicalModule {ι : Type*} (R : Type*) [Ring R] [TopologicalSpace R]
    {M : ι → Type*} [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    [∀ i, TopologicalSpace (M i)] [∀ i, IsTopologicalModule R (M i)] :
    IsTopologicalModule R ((i : ι) → M i) where
  continuous_smul := by apply continuous_smul
  continuous_add := by apply continuous_add

end IsTopologicalModuleDep


