/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/ArithmeticGeometry/code/AdeleQuotientDim.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.ArithmeticGeometry.code.RiemannRoch.Part6
import Lemma.Scheme.Atlas.v1.ArithmeticGeometry.code.RiemannRoch
import Mathlib.LinearAlgebra.Isomorphisms
import Mathlib.RingTheory.Finiteness.Finsupp
import Class.v1.Atlas.ArithmeticGeometry.code.AdeleQuotientDim
open scoped RestrictedProduct
open FunctionFieldAdeleRing DiscreteValuationFamily


/-- The residue field $\mathcal{O}_p/\mathfrak{m}_p$ at a place $p$ is a
$k$-algebra via the composition $k \to \mathcal{O}_p \twoheadrightarrow
\mathcal{O}_p/\mathfrak{m}_p$. -/
noncomputable instance residueFieldAlgebra {P : Type*} {F : Type*} {k : Type*}
    [Field k] [Field F] [Algebra k F] {O : P → ValuationSubring F}
    [ConstantField k (F := F) (P := P) (O := O)] (p : P) :
    Algebra k (IsLocalRing.ResidueField ↥(O p)) :=
  letI : Algebra k ↥(O p) :=
    ((algebraMap k F).codRestrict (O p).toSubring
      (fun c => ConstantField.algebraMap_mem (k := k) (O := O) p c)).toAlgebra
  (IsLocalRing.residue ↥(O p) |>.comp (algebraMap k ↥(O p))).toAlgebra

