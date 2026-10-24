/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/Buildings/code/Building/CoxeterComplexFoldings.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import sympy.atlas.v1.Atlas.Buildings.code.Building.AptIsCoxeterProof
import Lemma.Set.ApartmentsToApartmentSystem.eq.Apartments.of.IsThick
import Lemma.Nat.Any_And_EqAdd_1AndAll_Eq_Add_1.of.Gt.All_Eq_Add_1OrEqAdd_1.Eq_0
import sympy.atlas.v1.Atlas.Buildings.code.CoxeterGroup.DeletionCondition
import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Tactic.Group

open scoped Classical
open ChamberComplex
open Garrett.ExchangeDeletion
open AptIsCoxeterProof

variable {V : Type*} [DecidableEq V]

/-- A bundle of data realising a chamber complex $\mathcal{C}$ as the Coxeter
complex of a Coxeter system $(W, S)$: chambers are indexed by $W$, the chamber
map intertwines adjacency with right multiplication by simple reflections, the
complex is thin, and the exchange condition together with a folding-from-half
axiom holds. -/
structure CoxeterComplexData (V : Type*) [DecidableEq V] where
  cc : ChamberComplex V
  B : Type*
  M : CoxeterMatrix B
  cs : CoxeterSystem M M.Group
  chamberOf : M.Group → Finset V
  chamberOf_injective : Function.Injective chamberOf
  chamberOf_surj : ∀ C, cc.toSimplicialComplex.IsMaximal C → ∃ w, chamberOf w = C
  chamberOf_maximal : ∀ w, cc.toSimplicialComplex.IsMaximal (chamberOf w)
  adj_of_mul_simple : ∀ w i,
    cc.toSimplicialComplex.Adjacent (chamberOf w) (chamberOf (w * cs.simple i))
  adj_implies_mul_simple : ∀ w C,
    cc.toSimplicialComplex.Adjacent (chamberOf w) C →
    ∃ i, C = chamberOf (w * cs.simple i)
  thin : cc.IsThin
  exchange : SatisfiesExchangeCondition M cs
  folding_from_chamber_map :
    ∀ (f₀ : M.Group → M.Group),
      (∀ w, f₀ (f₀ w) = f₀ w) →
      (∀ w i, chamberOf (f₀ (w * cs.simple i)) = chamberOf (f₀ w) ∨
              cc.toSimplicialComplex.Adjacent
                (chamberOf (f₀ w)) (chamberOf (f₀ (w * cs.simple i)))) →
      (∃ w, f₀ w ≠ w) →
      (∀ w, f₀ w = w → ∃! w', w' ≠ w ∧ f₀ w' = w) →
      ∃ f : Folding cc, ∀ w, (chamberOf w).image f.morph.toFun = chamberOf (f₀ w)

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
