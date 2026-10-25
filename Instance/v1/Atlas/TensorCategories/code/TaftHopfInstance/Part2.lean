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
import Theorem.v1.Atlas.TensorCategories.code.TaftHopfInstance.Part2
open Coalgebra HopfAlgebra
open scoped TensorProduct


namespace TaftAlgebraType

variable (k : Type*) [Field k] (n : ℕ) [NeZero n] (q : k) [Fact (q ^ n = 1)]


local notation "A" => TaftAlgebraType n q k

variable [TaftHopfData k n q]

noncomputable section

/-- The Taft algebra is a coalgebra over `k`. -/
noncomputable instance taftCoalgebra [TaftHopfData k n q] :
    Coalgebra k A where
  coassoc := taft_coassoc k n q
  rTensor_counit_comp_comul := taft_rTensor_counit k n q
  lTensor_counit_comp_comul := taft_lTensor_counit k n q

/-- The Taft algebra is a bialgebra over `k`, built from compatible algebra and coalgebra
structures. -/
noncomputable instance taftBialgebra [TaftHopfData k n q] :
    Bialgebra k A :=
  Bialgebra.mk' k A
    (show taftCounitLM k n q (1 : A) = 1 from taft_counit_one k n q)
    (fun {a b} => show taftCounitLM k n q (a * b) = taftCounitLM k n q a * taftCounitLM k n q b
      from taft_counit_mul k n q a b)
    (show taftComulLM k n q (1 : A) = 1 from taft_comul_one k n q)
    (fun {a b} => show taftComulLM k n q (a * b) = taftComulLM k n q a * taftComulLM k n q b
      from taft_comul_mul k n q a b)

/-- `HopfAlgebraStruct k A` providing the antipode via `taftAntipodeLM`. -/
noncomputable instance taftHopfAlgebraStruct [TaftHopfData k n q] :
    HopfAlgebraStruct k A where
  antipode := taftAntipodeLM k n q

end
end TaftAlgebraType
