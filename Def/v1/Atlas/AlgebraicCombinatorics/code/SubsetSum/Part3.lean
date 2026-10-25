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
import Theorem.v1.Atlas.AlgebraicCombinatorics.code.SubsetSum.Part2
set_option autoImplicit false

open SpernerProperty YoungLattice YoungLattice.Lmn Finset


namespace SubsetSum

noncomputable def toLmn
    (S : Finset ℝ) (n : ℕ) (hScard : S.card = n)
    (T : Finset ℝ) (k : ℕ) (hTcard : T.card = k) (hTsub : T ⊆ S)
    (hkn : k ≤ n) : Lmn k (n - k) :=
  ⟨fun i => ⟨idxVal S n hScard T k hTcard hTsub (Fin.rev i) -
    (Fin.rev i).val, by
    have := idxVal_bound S n hScard T k hTcard hTsub hkn (Fin.rev i); omega⟩,
  fun a b hab => by
    simp only [Fin.le_def]
    have hrev := Fin.rev_le_rev.mpr hab
    have hsm : StrictMono (fun r => (idxFun S n hScard T k hTcard hTsub r).val) :=
      fun x y hxy => (idxFun_strictMono S n hScard T k hTcard hTsub).lt_iff_lt.mpr hxy
    have h := strictMono_fin_add_le hsm (Fin.rev b) (Fin.rev a) hrev
    have hge_a := idxVal_ge S n hScard T k hTcard hTsub (Fin.rev a)
    have hge_b := idxVal_ge S n hScard T k hTcard hTsub (Fin.rev b)
    simp only [idxVal] at *
    omega⟩

end SubsetSum
