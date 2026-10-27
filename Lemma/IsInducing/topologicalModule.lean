import Mathlib
import Class.Mathlib_IsModuleTopology


open Topology


protected theorem Topology.IsInducing.topologicalModule {F : Type*}
    (R : Type*) [Ring R] [TopologicalSpace R]
    {M : Type*} [AddCommGroup M] [Module R M] [TopologicalSpace M] [IsTopologicalModule R M]
    {H : Type*} [AddCommGroup H] [Module R H] [TopologicalSpace H]
    [FunLike F H M] [LinearMapClass F R H M] (f : F) (hf : IsInducing ⇑f) :
    IsTopologicalModule R H where
  continuous_smul :=
    (hf.continuousSMul (continuous_id : Continuous (id : R → R))
      (fun {c x} => map_smul f c x)).continuous_smul
  continuous_add := (Topology.IsInducing.continuousAdd f hf).continuous_add
