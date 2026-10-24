/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section9.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib.Algebra.FiveLemma
import Mathlib.Algebra.Homology.HomologySequence
import sympy.atlas.v1.Atlas.AlgebraicTopologyI.code.Section11
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section11

open CategoryTheory

namespace HomologyLongExactSequence

variable {C ι : Type*} [Category C] [Abelian C] {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}

/-- The connecting (boundary) homomorphism `∂ : Hᵢ(C) ⟶ Hⱼ(A)` associated with a short exact
sequence `0 → A → B → C → 0` of chain complexes, where `j` is the index reached from `i`
under the complex shape. This is the key map appearing in the homology long exact sequence
(Theorem 9.1). -/
noncomputable def connectingHomomorphism
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    S.X₃.homology i ⟶ S.X₁.homology j :=
  ShortComplex.ShortExact.δ hS i j hij

/-- Exactness of the long exact sequence at the middle term `Hᵢ(B)`: the image of
`Hᵢ(A) → Hᵢ(B)` equals the kernel of `Hᵢ(B) → Hᵢ(C)` for a short exact sequence of
chain complexes. -/
theorem exact_f_g (hS : S.ShortExact) (i : ι) :
    (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact :=
  ShortComplex.ShortExact.homology_exact₂ hS i

/-- Exactness of the long exact sequence at `Hᵢ(C)`: the image of `Hᵢ(B) → Hᵢ(C)` equals
the kernel of the connecting map `∂ : Hᵢ(C) → Hⱼ(A)`. -/
theorem exact_g_δ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₃ hS i j hij

/-- Exactness of the long exact sequence at `Hⱼ(A)`: the image of the connecting map
`∂ : Hᵢ(C) → Hⱼ(A)` equals the kernel of `Hⱼ(A) → Hⱼ(B)`. -/
theorem exact_δ_f (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact :=
  ShortComplex.ShortExact.homology_exact₁ hS i j hij

/-- Packaged data for the homology long exact sequence (Theorem 9.1): the connecting
homomorphism `δ` and the three exactness statements (at `Hᵢ(B)`, at `Hᵢ(C)`, and at
`Hⱼ(A)`) for a short exact sequence of chain complexes. -/
structure HomologyLongExactSequenceData (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) where
  δ : S.X₃.homology i ⟶ S.X₁.homology j
  exact_at_X₂ : (ShortComplex.mk
      (HomologicalComplex.homologyMap S.f i)
      (HomologicalComplex.homologyMap S.g i) (by
        rw [← HomologicalComplex.homologyMap_comp, S.zero,
          HomologicalComplex.homologyMap_zero])).Exact
  exact_at_X₃ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.comp_δ hS i j hij)).Exact
  exact_at_X₁ : (ShortComplex.mk _ _ (ShortComplex.ShortExact.δ_comp hS i j hij)).Exact

/-- **Theorem 9.1** (Homology long exact sequence). Given a short exact sequence
`0 → A → B → C → 0` of chain complexes, there is a natural connecting homomorphism
`∂ : Hₙ(C) → Hₙ₋₁(A)` such that
`⋯ → Hₙ(A) → Hₙ(B) → Hₙ(C) →∂ Hₙ₋₁(A) → ⋯`
is exact. This bundles the connecting map together with exactness at each spot. -/
noncomputable def homologyLongExactSequence
    (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j) :
    HomologyLongExactSequenceData hS i j hij where
  δ := connectingHomomorphism hS i j hij
  exact_at_X₂ := exact_f_g hS i
  exact_at_X₃ := exact_g_δ hS i j hij
  exact_at_X₁ := exact_δ_f hS i j hij

end HomologyLongExactSequence

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

attribute [instance] LongExactLadder.grpA LongExactLadder.grpA' LongExactLadder.grpB
  LongExactLadder.grpB' LongExactLadder.grpC LongExactLadder.grpC'

namespace LongExactLadder

variable (L : LongExactLadder)

/-- Forgetting the subspace data: a map of pairs `(X, A) → (Y, B)` induces a map between
the trivial pairs `(X, ∅) → (Y, ∅)`. Used in the Eilenberg–Steenrod packaging. -/
def MapOfPairs.toSpaceMap {P Q : TopPair} (f : MapOfPairs P Q) :
    MapOfPairs (TopPair.ofSpace P.space) (TopPair.ofSpace Q.space) where
  toFun := f.toFun
  continuous_toFun := f.continuous_toFun
  mapsTo := fun _ h => h.elim

end EilenbergSteenrod
