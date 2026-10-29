/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Topology/MetricSpace/HausdorffDimensionFunction.lean -/

import Mathlib.Topology.Order.Hom.Basic
import Mathlib.Topology.UniformSpace.Real
import Structure.Topology.MetricSpace.HausdorffDimensionFunction
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

