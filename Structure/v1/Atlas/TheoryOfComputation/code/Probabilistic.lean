/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

module

public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Algebra.Polynomial.Roots
public import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
public import Mathlib.Algebra.MvPolynomial.SchwartzZippel
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Data.Nat.Prime.Infinite
public import Mathlib.Algebra.Order.Archimedean.Basic


public section

namespace Probabilistic

/-- A formal description of a pair of finite simple graphs `(G, H)`, packaged
together with the decidability and finiteness instances needed to manipulate
them constructively. Used as the underlying mathematical object for the graph
isomorphism problem `ISO`. -/
structure GraphPairDesc where
  V : Type
  instFintypeV : Fintype V
  instDecEqV : DecidableEq V
  G : SimpleGraph V
  instDecRelG : DecidableRel G.Adj
  W : Type
  instFintypeW : Fintype W
  instDecEqW : DecidableEq W
  H : SimpleGraph W
  instDecRelH : DecidableRel H.Adj

end Probabilistic
