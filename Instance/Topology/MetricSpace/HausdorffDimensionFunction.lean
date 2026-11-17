/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean -/

module

public import Mathlib.Topology.Order.Hom.Basic
public import Mathlib.Topology.UniformSpace.Real
public import Structure.Topology.MetricSpace.HausdorffDimensionFunction

@[expose] public section

open scoped NNReal Topology
open Filter


instance : FunLike HausdorffDimensionFunction NNReal NNReal where
  coe ψ := ψ.toContinuousOrderHom
  coe_injective ψ φ h := by
    cases ψ
    cases φ
    simp only [HausdorffDimensionFunction.mk.injEq]
    exact ContinuousOrderHom.ext fun r ↦ congrFun h r

instance : ContinuousOrderHomClass HausdorffDimensionFunction NNReal NNReal where
  map_monotone ψ := ψ.toContinuousOrderHom.monotone
  map_continuous ψ := ψ.toContinuousOrderHom.continuous_toFun

