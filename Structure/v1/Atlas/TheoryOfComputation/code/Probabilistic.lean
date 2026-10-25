/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TheoryOfComputation/code/Probabilistic.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Algebra.Polynomial.Roots
import Def.v1.Atlas.TheoryOfComputation.code.BPP.Part3
import Mathlib.Algebra.MvPolynomial.SchwartzZippel
import Mathlib.Algebra.MvPolynomial.CommRing
import Mathlib.Data.Nat.Prime.Infinite
import Mathlib.Algebra.Order.Archimedean.Basic


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
