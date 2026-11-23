module

public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.Analysis.Normed.Module.Basic
public import Mathlib.Analysis.Normed.Group.Basic
public import Mathlib.Data.Vector.Basic
public import Mathlib.Topology.UniformSpace.UniformEmbedding
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Theorem.Vector.Zero.eq.Replicate
public import Theorem.Tensor.Eq.is.EqDataS
public import Instance.Data.Tensor.Tensor.Part2
public import Inductive.MeasureTheory.Integral.IntervalIntegral.Integrals

@[expose] public section

open Tensor


def ℒ : LSpace := .mk

