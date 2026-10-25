/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/TaftHopfInstance.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.TensorCategories.code.TaftConcrete.Part4
import Lemma.Category.Atlas.v1.TensorCategories.code.TaftConcrete
import Def.v1.Atlas.TensorCategories.code.HopfAlgebraExamples.Part2
import Class.v1.Atlas.TensorCategories.code.TaftHopfInstance
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

set_option checkBinderAnnotations false in
/-- Extract the inequality `n ≥ 2` from `TaftHopfData`. -/
def hn2' [TaftHopfData k n q] : n ≥ 2 :=
  TaftHopfData.hn2 (k := k) (q := q)

/-- The comultiplication on the Taft algebra extracted from the existential `hopf_axioms`. -/
def taftComulLM [TaftHopfData k n q] : A →ₗ[k] A ⊗[k] A :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose

/-- The counit on the Taft algebra extracted from `hopf_axioms`. -/
def taftCounitLM [TaftHopfData k n q] : A →ₗ[k] k :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose_spec.choose

/-- The antipode on the Taft algebra extracted from `hopf_axioms`. -/
def taftAntipodeLM [TaftHopfData k n q] : A →ₗ[k] A :=
  (TaftHopfData.hopf_axioms (k := k) (n := n) (q := q)).choose_spec.choose_spec.choose

end
end TaftAlgebraType
