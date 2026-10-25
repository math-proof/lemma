/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
import Lemma.Nat.Any_And_EqAdd_1AndAll_Eq_Add_1.of.Gt.All_Eq_Add_1OrEqAdd_1.Eq_0
import Def.v1.Atlas.Buildings.code.CoxeterGroup.DeletionCondition
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Tactic.Group
import Structure.v1.Atlas.Buildings.code.Building.CoxeterComplexFoldings
open scoped Classical
open ChamberComplex
open Garrett.ExchangeDeletion
open AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]


namespace CoxeterComplexData

variable (data : CoxeterComplexData V)

/-- The half-fold map $f_0^s : W \to W$ associated to a simple reflection $s$:
elements $w$ with $\ell(sw) = \ell(w) + 1$ are fixed (the positive half), and
elements with $\ell(sw) = \ell(w) - 1$ are sent to $sw$ (collapsing the
negative half onto the positive half). -/
noncomputable def chamberMapF₀ (s : data.B) (w : data.M.Group) : data.M.Group :=
  if data.cs.length (data.cs.simple s * w) = data.cs.length w + 1
  then w
  else data.cs.simple s * w

/-- $w$ lies in the positive half-space of the wall associated to $s$, i.e.
$\ell(sw) = \ell(w) + 1$. -/
def inPositiveHalf (s : data.B) (w : data.M.Group) : Prop :=
  data.cs.length (data.cs.simple s * w) = data.cs.length w + 1

/-- $w$ lies in the negative half-space of the wall associated to $s$, i.e.
$\ell(sw) + 1 = \ell(w)$. -/
def inNegativeHalf (s : data.B) (w : data.M.Group) : Prop :=
  data.cs.length (data.cs.simple s * w) + 1 = data.cs.length w

/-- The conjugate $u \mapsto w \cdot f_0^s(w^{-1}u)$ of the half-fold map by
left translation by $w$ — gives the folding that pairs the chambers $C_w$ and
$C_{ws}$. -/
noncomputable def conjugatedF₀ (w : data.M.Group) (s : data.B)
    (u : data.M.Group) : data.M.Group :=
  w * data.chamberMapF₀ s (w⁻¹ * u)

end CoxeterComplexData
