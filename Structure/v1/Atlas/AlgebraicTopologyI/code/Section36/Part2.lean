/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section36.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Theorem.v1.Atlas.AlgebraicTopologyI.code.Section34.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section34
import Mathlib.AlgebraicTopology.SingularHomology.Basic
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Colimits
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.Algebra.Homology.ShortComplex.Linear
import Mathlib.Algebra.Homology.HomologySequence
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Topology.Category.TopCat.Basic
import Mathlib.Topology.Separation.Regular
import Mathlib.Algebra.Group.Subgroup.Ker
import Def.v1.Atlas.AlgebraicTopologyI.code.Section36.Part13
open CategoryTheory AlgebraicTopology Limits TopologicalSpace MonoidalCategory


noncomputable section

open Set FullyRelativeCapProduct

/-- Data witnessing the Čech/singular Mayer–Vietoris compatibility ladder of
Theorem 36.2: a Mayer–Vietoris sequence in Čech cohomology of `A, B, A ∪ B,
A ∩ B`, a Mayer–Vietoris sequence in relative singular homology of their
complements, exactness of both sequences, "cap rungs" connecting them indexed
by subsets `S ∈ {A, B, A ∪ B, A ∩ B}` for each `(p, q)` with `p + q = n`, and
three commutative squares expressing compatibility with the union-to-sum,
sum-to-intersection, and connecting morphisms. -/
structure MayerVietorisLadder (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n) where

  topUnionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  topSumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  topConnecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))

  botUnionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  botSumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  botConnecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)

  top_exact_sum : ∀ p : ℕ, Function.Exact
    (topUnionToSum p).hom (topSumToInter p).hom
  top_exact_inter : ∀ p : ℕ, Function.Exact
    (topSumToInter p).hom (topConnecting p).hom
  top_exact_union : ∀ p : ℕ, Function.Exact
    (topConnecting p).hom (topUnionToSum (p + 1)).hom

  bot_exact_sum : ∀ q : ℕ, Function.Exact
    (botUnionToSum q).hom (botSumToInter q).hom
  bot_exact_inter : ∀ q : ℕ, Function.Exact
    (botSumToInter q).hom (botConnecting q).hom
  bot_exact_union : ∀ q : ℕ, Function.Exact
    (botConnecting q).hom (botUnionToSum (q - 1)).hom

  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ botUnionToSum q =
      topUnionToSum p ≫ Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫ botSumToInter q =
      topSumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    topConnecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ botConnecting q

/-- Abstract data of a Mayer–Vietoris long exact sequence in Čech cohomology
for the cover `A, B` of `A ∪ B`: a union-to-sum map, a sum-to-intersection
map, a degree-raising connecting morphism, and the three exactness conditions
making the resulting sequence long exact. -/
structure CechMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ p : ℕ,
    (cechCohomology R X (A ∪ B) p ⟶
      cechCohomology R X A p ⊞ cechCohomology R X B p)
  sumToInter : ∀ p : ℕ,
    (cechCohomology R X A p ⊞ cechCohomology R X B p ⟶
      cechCohomology R X (A ∩ B) p)
  connecting : ∀ p : ℕ,
    (cechCohomology R X (A ∩ B) p ⟶ cechCohomology R X (A ∪ B) (p + 1))
  exact_sum : ∀ p : ℕ, Function.Exact
    (unionToSum p).hom (sumToInter p).hom
  exact_inter : ∀ p : ℕ, Function.Exact
    (sumToInter p).hom (connecting p).hom
  exact_union : ∀ p : ℕ, Function.Exact
    (connecting p).hom (unionToSum (p + 1)).hom

/-- Abstract data of a Mayer–Vietoris long exact sequence in relative singular
homology for the cover `A, B` of `A ∪ B` (taken in the complements): a
union-to-sum map, a sum-to-intersection map, a degree-lowering connecting
morphism, and the three exactness conditions. -/
structure SingularMVSequence (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) where
  unionToSum : ∀ q : ℕ,
    (relSingularHomology R X (A ∪ B)ᶜ q ⟶
      relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q)
  sumToInter : ∀ q : ℕ,
    (relSingularHomology R X Aᶜ q ⊞ relSingularHomology R X Bᶜ q ⟶
      relSingularHomology R X (A ∩ B)ᶜ q)
  connecting : ∀ q : ℕ,
    (relSingularHomology R X (A ∩ B)ᶜ q ⟶ relSingularHomology R X (A ∪ B)ᶜ (q - 1))
  exact_sum : ∀ q : ℕ, Function.Exact
    (unionToSum q).hom (sumToInter q).hom
  exact_inter : ∀ q : ℕ, Function.Exact
    (sumToInter q).hom (connecting q).hom
  exact_union : ∀ q : ℕ, Function.Exact
    (connecting q).hom (unionToSum (q - 1)).hom

/-- The "cap rung" data connecting a Čech Mayer–Vietoris sequence to a
singular Mayer–Vietoris sequence in the presence of a fixed homology class
`x_union ∈ H_n(X, (A ∪ B)ᶜ)`: cap product maps for each subset
`S ∈ {A, B, A ∪ B, A ∩ B}` and `(p, q)` with `p + q = n`, plus the three
commutative squares expressing Mayer–Vietoris naturality. -/
structure MVCapProductData (R : Type) [CommRing R]
    (X : TopCat.{0}) (A B : Set X) (n : ℕ)
    (x_union : relSingularHomology R X (A ∪ B)ᶜ n)
    (cechMV : CechMVSequence R X A B)
    (singMV : SingularMVSequence R X A B) where
  capRung : ∀ (p q : ℕ) (S : Set X), p + q = n →
    (cechCohomology R X S p ⟶ relSingularHomology R X Sᶜ q)
  comm_sq1 : ∀ (p q : ℕ) (hpq : p + q = n),
    capRung p q (A ∪ B) hpq ≫ singMV.unionToSum q =
      cechMV.unionToSum p ≫
        Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq)
  comm_sq2 : ∀ (p q : ℕ) (hpq : p + q = n),
    Limits.biprod.map (capRung p q A hpq) (capRung p q B hpq) ≫
      singMV.sumToInter q =
      cechMV.sumToInter p ≫ capRung p q (A ∩ B) hpq
  comm_sq3 : ∀ (p q : ℕ) (hpq : p + q = n) (hpq' : (p + 1) + (q - 1) = n),
    cechMV.connecting p ≫ capRung (p + 1) (q - 1) (A ∪ B) hpq' =
      capRung p q (A ∩ B) hpq ≫ singMV.connecting q

end
