/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Exact3D/RandomCurrentPredecessorComparison.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.Exact3D.BoxPathWitness.Part4
import Theorem.StatisticalMechanics.Code.Exact3D.FKPositiveSubcriticalQ2Bridge.Part121
import Theorem.StatisticalMechanics.Code.FK.QuadrantPartition.Part9
import Theorem.StatisticalMechanics.Code.Exact3D.RandomCurrentPredecessorComparison.Part8
open scoped BigOperators symmDiff
open MeasureTheory

set_option linter.style.longLine false


namespace StatMech

namespace Exact3D

noncomputable def doubledBoxOriginToInnerEndpointEdgeCopyCollapsedMultiplicity
    (n : ℕ) (v : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  edgeCopySourcePairEmptyCollapsedMultiplicity (FK.boxGraph 3 (2 * n))
    (doubledBoxOriginToInnerEndpointSource n v) m


noncomputable def edgeCopySourcePairEmptyCollapsedTerm
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (β : ℝ) (J : Sym2 V → ℝ) (A : Finset V)
    (m : ↥G.edgeFinset → ℕ) : ℝ :=
  edgeCopySourcePairEmptyCollapsedMultiplicity G A m *
    Sharpness.weight G β J (Sharpness.ofEdgeFun G m)


noncomputable def doubledBoxOriginToInnerEndpointEdgeCopyCollapsedTerm
    (β : ℝ) (n : ℕ) (v : FK.boxVerts 3 n)
    (m : ↥(FK.boxGraph 3 (2 * n)).edgeFinset → ℕ) : ℝ :=
  edgeCopySourcePairEmptyCollapsedTerm (FK.boxGraph 3 (2 * n)) β (fun _ => 1)
    (doubledBoxOriginToInnerEndpointSource n v) m


end Exact3D
end StatMech
