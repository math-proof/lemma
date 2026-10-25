/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierB/OneDimDLRUniqueness.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.StatisticalMechanics.Code.FrontierB.OneDimFiniteVolumeBridge.Part18
import Theorem.StatisticalMechanics.Code.Ising.GibbsSimplexInfinite.Part3
import Def.StatisticalMechanics.Code.FrontierB.OneDimDLRUniqueness
open scoped BigOperators
open Finset Matrix


namespace StatMech.FrontierB

lemma pathCastEquiv_apply (E : Type*) {m n : ℕ} (h : m = n)
    (q : Fin m → E) (i : Fin n) :
    pathCastEquiv E h q i = q (Fin.cast h.symm i) := by
  rfl

lemma pathCastEquiv_symm_apply (E : Type*) {m n : ℕ} (h : m = n)
    (q : Fin n → E) (i : Fin m) :
    (pathCastEquiv E h).symm q i = q (Fin.cast h i) := by
  subst n
  rfl

lemma openMatrixProduct_pathCast {E R : Type*} [Fintype E] [DecidableEq E]
    [CommSemiring R] (A : Matrix E E R) (a b : E) {m n : ℕ}
    (h : m = n) (q : Fin m → E) :
    openMatrixProduct A a b (pathCastEquiv E h q) = openMatrixProduct A a b q := by
  subst n
  rfl

end StatMech.FrontierB
