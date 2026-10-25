/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequence
import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11
import Def.v1.Atlas.AlgebraicTopologyI.code.Section9.Part2
open CategoryTheory


namespace FiveLemma

variable {A₁ A₂ A₃ A₄ A₅ B₁ B₂ B₃ B₄ B₅ : Type*}

variable [AddCommGroup A₁] [AddCommGroup A₂] [AddCommGroup A₃]
  [AddCommGroup A₄] [AddCommGroup A₅]

variable [AddCommGroup B₁] [AddCommGroup B₂] [AddCommGroup B₃]
  [AddCommGroup B₄] [AddCommGroup B₅]

/-- A "homology ladder": a commutative ladder of two long exact sequences (with maps
`i`, `p`, `δ` on each row) of graded abelian groups indexed by `ℤ`, together with
vertical chain maps `fMap`, `gMap`, `hMap` between corresponding groups. This is the
algebraic setup used to apply the five lemma degree-by-degree (Proposition 9.4). -/
structure HomologyLadder where
  HA : ℤ → Type*
  HB : ℤ → Type*
  HC : ℤ → Type*
  HA' : ℤ → Type*
  HB' : ℤ → Type*
  HC' : ℤ → Type*
  [grpHA : ∀ n, AddCommGroup (HA n)]
  [grpHB : ∀ n, AddCommGroup (HB n)]
  [grpHC : ∀ n, AddCommGroup (HC n)]
  [grpHA' : ∀ n, AddCommGroup (HA' n)]
  [grpHB' : ∀ n, AddCommGroup (HB' n)]
  [grpHC' : ∀ n, AddCommGroup (HC' n)]
  iMap : ∀ n, HA n →+ HB n
  pMap : ∀ n, HB n →+ HC n
  δ : ∀ n, HC (n + 1) →+ HA n
  iMap' : ∀ n, HA' n →+ HB' n
  pMap' : ∀ n, HB' n →+ HC' n
  δ' : ∀ n, HC' (n + 1) →+ HA' n
  fMap : ∀ n, HA n →+ HA' n
  gMap : ∀ n, HB n →+ HB' n
  hMap : ∀ n, HC n →+ HC' n
  exact_ip : ∀ n, Function.Exact (iMap n) (pMap n)
  exact_pδ : ∀ n, Function.Exact (pMap (n + 1)) (δ n)
  exact_δi : ∀ n, Function.Exact (δ n) (iMap n)
  exact_i'p' : ∀ n, Function.Exact (iMap' n) (pMap' n)
  exact_p'δ' : ∀ n, Function.Exact (pMap' (n + 1)) (δ' n)
  exact_δ'i' : ∀ n, Function.Exact (δ' n) (iMap' n)
  comm_fi : ∀ n, (iMap' n).comp (fMap n) = (gMap n).comp (iMap n)
  comm_gp : ∀ n, (pMap' n).comp (gMap n) = (hMap n).comp (pMap n)
  comm_hδ : ∀ n, (δ' n).comp (hMap (n + 1)) = (fMap n).comp (δ n)

attribute [instance] HomologyLadder.grpHA HomologyLadder.grpHB HomologyLadder.grpHC
  HomologyLadder.grpHA' HomologyLadder.grpHB' HomologyLadder.grpHC'

/-- A ladder of two long exact sequences (with maps `ι`, `π`, `δ` on each row), connected
by vertical maps `fA`, `fB`, `fC`. This is a streamlined presentation of the data needed
for the 2-out-of-3 isomorphism principle in homology (Corollary 9.5 and Proposition 9.6). -/
structure LongExactLadder where
  A  : ℤ → Type*
  A' : ℤ → Type*
  B  : ℤ → Type*
  B' : ℤ → Type*
  C  : ℤ → Type*
  C' : ℤ → Type*
  [grpA  : ∀ n, AddCommGroup (A n)]
  [grpA' : ∀ n, AddCommGroup (A' n)]
  [grpB  : ∀ n, AddCommGroup (B n)]
  [grpB' : ∀ n, AddCommGroup (B' n)]
  [grpC  : ∀ n, AddCommGroup (C n)]
  [grpC' : ∀ n, AddCommGroup (C' n)]
  ι  : ∀ n, A n →+ B n
  π  : ∀ n, B n →+ C n
  δ  : ∀ n, C (n + 1) →+ A n
  ι' : ∀ n, A' n →+ B' n
  π' : ∀ n, B' n →+ C' n
  δ' : ∀ n, C' (n + 1) →+ A' n
  fA : ∀ n, A n →+ A' n
  fB : ∀ n, B n →+ B' n
  fC : ∀ n, C n →+ C' n
  exact_δι : ∀ n, Function.Exact (δ n) (ι n)
  exact_ιπ : ∀ n, Function.Exact (ι n) (π n)
  exact_πδ : ∀ n, Function.Exact (π (n + 1)) (δ n)
  exact_δ'ι' : ∀ n, Function.Exact (δ' n) (ι' n)
  exact_ι'π' : ∀ n, Function.Exact (ι' n) (π' n)
  exact_π'δ' : ∀ n, Function.Exact (π' (n + 1)) (δ' n)
  comm_ι : ∀ n, (ι' n).comp (fA n) = (fB n).comp (ι n)
  comm_π : ∀ n, (π' n).comp (fB n) = (fC n).comp (π n)
  comm_δ : ∀ n, (δ' n).comp (fC (n + 1)) = (fA n).comp (δ n)

end FiveLemma
