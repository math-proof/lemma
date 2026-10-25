/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/SubsetSum.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Instance.v1.Atlas.AlgebraicCombinatorics.code.YoungLattice.Part3
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLattice
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.YoungLatticeSperner
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.QBinomial
import Lemma.Finset.Atlas.v1.AlgebraicCombinatorics.code.GroupActions
import Def.v1.Atlas.AlgebraicCombinatorics.code.YoungLatticeSperner.Part3
import Def.v1.Atlas.AlgebraicCombinatorics.code.QBinomial.Part2
import Abbrev.v1.Atlas.AlgebraicCombinatorics.code.GroupActions
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.SubsetSum
set_option autoImplicit false

open SpernerProperty YoungLattice YoungLattice.Lmn Finset


namespace SubsetSum

noncomputable def lambdaMapForward (k m : ℕ) (p : Lmn k m) : Finset ℕ :=
  (Finset.univ : Finset (Fin k)).image (fun r => (p.val (Fin.rev r)).val + r.val + 1)

noncomputable def idxFun
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : Fin n :=
  (S.orderIsoOfFin hScard).symm
    ⟨T.orderEmbOfFin hTcard r, hTsub (Finset.orderEmbOfFin_mem T hTcard r)⟩

noncomputable def idxVal
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (r : Fin k) : ℕ :=
  (idxFun S n hScard T k hTcard hTsub r).val

end SubsetSum
