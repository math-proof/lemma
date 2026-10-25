/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/CoxeterGroup/TypeACoxeterSystem.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.GroupTheory.Coxeter.Basic
import Mathlib.GroupTheory.Coxeter.Matrix
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.GroupTheory.Perm.Fin
import Mathlib.GroupTheory.Perm.Support
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeAInjectivityHelper
import Theorem.v1.Atlas.Buildings.code.CoxeterGroup.TypeACoxeterSystem
open Equiv Fin


namespace SymGroupCoxeter

/-- The canonical homomorphism from the abstract type-$A$ Coxeter group to $S_{n+1}$ sending
each Coxeter generator to the corresponding adjacent transposition. -/
noncomputable def toPermHom (n : ℕ) :
    (CoxeterMatrix.A n).Group →* Equiv.Perm (Fin (n + 1)) :=
  PresentedGroup.toGroup (adjTransp_relations_satisfied n)

/-- Group isomorphism $S_{n+1} \cong W(A_{n-1})$, the type-$A_{n-1}$ Coxeter group. -/
noncomputable def symGroup_mulEquiv (n : ℕ) :
    Equiv.Perm (Fin (n + 1)) ≃* (CoxeterMatrix.A n).Group :=
  typeA_symGroup_mulEquiv n

/-- The canonical type-$A$ Coxeter system structure on $S_{n+1}$. -/
noncomputable def symGroup_coxeterSystem (n : ℕ) :
    CoxeterSystem (CoxeterMatrix.A n) (Equiv.Perm (Fin (n + 1))) :=
  ⟨symGroup_mulEquiv n⟩

end SymGroupCoxeter
