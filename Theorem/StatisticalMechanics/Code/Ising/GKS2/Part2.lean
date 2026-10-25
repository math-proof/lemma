/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GKS2.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib
import Theorem.StatisticalMechanics.Code.Ising.GKS.Part5
import Def.StatisticalMechanics.Code.Ising.GKS2
open scoped BigOperators symmDiff
open Finset

set_option linter.style.show false
set_option linter.unusedSectionVars false

set_option linter.unusedSectionVars false
set_option linter.unusedFintypeInType false
set_option linter.unusedDecidableInType false
set_option linter.style.longLine false


namespace StatMech

namespace Ising

variable {V : Type*} [Fintype V] [DecidableEq V]


omit [Fintype V] [DecidableEq V] in

lemma spin_xnor (σ q : ConfigSpace V) (x : V) :
    spin (xnor σ q) x = spin σ x * spin q x := by
  unfold spin xnor
  by_cases h1 : σ x <;> by_cases h2 : q x <;> simp [h1, h2]

omit [Fintype V] [DecidableEq V] in

lemma bond_xnor (σ q : ConfigSpace V) (e : Sym2 V) :
    bond (xnor σ q) e = bond σ e * bond q e := by
  induction e with
  | h a b => rw [bond_mk, bond_mk, bond_mk, spin_xnor, spin_xnor]; ring

omit [Fintype V] in


lemma spinProd_xnor (B : Finset V) (σ q : ConfigSpace V) :
    spinProd B (xnor σ q) = spinProd B σ * spinProd B q := by
  unfold spinProd
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl (fun x _ => spin_xnor σ q x)


end Ising
end StatMech
