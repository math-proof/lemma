import Mathlib
import sympy.Basic
import sympy.atlas.Combinatorics.Words.CobhamUniformMorphism
open MetaMathlibExt


/--
[cobham_automatic_iff_uniform_morphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma cobham_automatic_iff_uniform_morphic_eq
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsKAutomaticSequence k w ↔ IsCodingOfProlongableKUniformFixedPoint k w := by
-- proof
  apply MetaMathlibExt.cobham_automatic_iff_uniform_morphic w hk

/--
[isCodingOfProlongableKUniformFixedPoint_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma isCodingOfProlongableKUniformFixedPoint_iff_eq
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (hk : 2 ≤ k) :
-- imply
  IsCodingOfProlongableKUniformFixedPoint k w ↔
    ∃ q : Nat, ∃ f : Fin q → List (Fin q), (∀ x, (f x).length = k) ∧
    ∃ a : Fin q, ∃ u : Nat → Fin q, ∃ g : Fin q → B,
    IsPrefixPreserving f a ∧ IsOmegaLimit f a u ∧ ∀ n, w n = g (u n) := by
-- proof
  apply MetaMathlibExt.isCodingOfProlongableKUniformFixedPoint_iff w hk

/--
[IsCodingOfProlongableKUniformFixedPoint.exists_isMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma IsCodingOfProlongableKUniformFixedPoint_exists_isMorphic_eq
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (h : IsCodingOfProlongableKUniformFixedPoint k w) :
-- imply
  ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w := by
-- proof
  apply MetaMathlibExt.IsCodingOfProlongableKUniformFixedPoint.exists_isMorphic h

/--
[IsKAutomaticSequence.exists_isMorphic](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Combinatorics/Words/CobhamUniformMorphism.lean)
-/
@[path]
private lemma IsKAutomaticSequence_exists_isMorphic_eq
  [Fintype B]
  {k : Nat}
  {w : Nat → B}
-- given
  (h : IsKAutomaticSequence k w) :
-- imply
  ∃ q : Nat, ∃ u : Nat → Fin q, ∃ g : Fin q → B, IsMorphic u g w := by
-- proof
  apply MetaMathlibExt.IsKAutomaticSequence.exists_isMorphic h


-- created on 2026-10-20
