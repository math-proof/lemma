/- https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicTopologyI/code/Section11.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Def.v1.Atlas.AlgebraicTopologyI.code.Section1.Part3
import Lemma.Set.Atlas.v1.AlgebraicTopologyI.code.Section1
import Mathlib.Topology.Basic
import Mathlib.Topology.Homotopy.Basic
import Mathlib.Algebra.Exact
import Mathlib.Algebra.DirectSum.Basic
import Mathlib.Algebra.Module.Prod
import Def.v1.Atlas.AlgebraicTopologyI.code.Section11.Part3
open Set Topology

universe u


namespace EilenbergSteenrod

attribute [instance] TopPair.instTop

/-- A triple `(X, A, U)` with `U ⊆ A ⊆ X` is *excisive* if the closure of `U` lies inside
the interior of `A` (Definition 10.1). For such a triple, the excision inclusion
`(X − U, A − U) ↪ (X, A)` is required to be a homology isomorphism. -/
structure IsExcisiveTriple (P : TopPair) (U : Set P.space) : Prop where
  sub_mem : U ⊆ P.sub
  closure_sub_interior : closure U ⊆ interior P.sub

/-- **Definition 11.1 (Eilenberg–Steenrod axioms).** A homology theory on `Top` consists of
a sequence of functors `Hₙ : Top₂ → Ab` (`n ∈ ℤ`) together with natural boundary maps
`∂ : Hₙ(X, A) → Hₙ₋₁(A, ∅)` satisfying:

1. **Homotopy invariance** — homotopic maps of pairs induce equal maps on `Hₙ`.
2. **Excision** — excisive inclusions induce isomorphisms in homology.
3. **Long exact sequence** — for every pair `(X, A)` the sequence
   `⋯ → Hₙ(A) → Hₙ(X) → Hₙ(X, A) → Hₙ₋₁(A) → ⋯` is exact.
4. **Dimension axiom** — `Hₙ(pt)` vanishes for `n ≠ 0`.
5. **Milnor (additivity) axiom** — for any disjoint union `∐ᵢ Xᵢ`, the canonical map
   `⨁ᵢ Hₙ(Xᵢ) → Hₙ(∐ᵢ Xᵢ)` is an isomorphism. -/
structure HomologyTheory where
  H : ℤ → TopPair → Type u
  instAddCommGroup : ∀ (n : ℤ) (P : TopPair), AddCommGroup (H n P)
  map : ∀ (n : ℤ) {P Q : TopPair}, MapOfPairs P Q → (H n P →+ H n Q)
  map_id : ∀ (n : ℤ) (P : TopPair), map n (MapOfPairs.id P) = AddMonoidHom.id (H n P)
  map_comp : ∀ (n : ℤ) {P Q R : TopPair} (f : MapOfPairs P Q) (g : MapOfPairs Q R),
    map n (g.comp f) = (map n g).comp (map n f)
  boundary : ∀ (n : ℤ) (P : TopPair), H (n + 1) P →+ H n P.subPair
  boundary_natural : ∀ (n : ℤ) {P Q : TopPair} (f : MapOfPairs P Q),
    (map n f.restrictToSub).comp (boundary n P) = (boundary n Q).comp (map (n + 1) f)
  homotopy_invariance : ∀ (n : ℤ) {P Q : TopPair} (f₀ f₁ : MapOfPairs P Q),
    AreHomotopic f₀ f₁ → map n f₀ = map n f₁
  excision : ∀ (n : ℤ) (P : TopPair) (U : Set P.space),
    IsExcisiveTriple P U → Function.Bijective (map n (excisionInclusion P U))
  exact_at_sub : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (boundary n P) (map n (inclusionSubToSpace P))
  exact_at_space : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (map n (inclusionSubToSpace P)) (map n (inclusionSpaceToPair P))
  exact_at_pair : ∀ (n : ℤ) (P : TopPair),
    Function.Exact (map (n + 1) (inclusionSpaceToPair P)) (boundary n P)
  dimension : ∀ (n : ℤ), n ≠ 0 → Subsingleton (H n TopPair.point)
  coproduct : ∀ (n : ℤ) {ι : Type u} [DecidableEq ι] (X : ι → Type u)
    [∀ i, TopologicalSpace (X i)],
    Function.Bijective
      (DirectSum.toAddMonoid (β := fun i => H n (TopPair.ofSpace (X i)))
        (fun i => map n (coproductInclusion ι X i)))

end EilenbergSteenrod
