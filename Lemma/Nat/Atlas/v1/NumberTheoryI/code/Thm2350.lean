import Mathlib
import Initialize.Tactic.Attr.Basic
open CategoryTheory Category


/--
[homology_les_exact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2350.lean)
-/
@[path]
lemma homology_les_exact
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S : ShortComplex (HomologicalComplex C c)}
-- given
  (hS : S.ShortExact)
  (i j : ι)
  (hij : c.Rel i j) :
-- imply
  (HomologicalComplex.HomologySequence.composableArrows₅ hS i j hij).Exact :=
-- proof
  HomologicalComplex.HomologySequence.composableArrows₅_exact hS i j hij

/--
[homology_les_naturality](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2350.lean)
-/
@[path]
lemma homology_les_naturality
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)}
  (φ : S₁ ⟶ S₂)
-- given
  (hS₁ : S₁.ShortExact)
  (hS₂ : S₂.ShortExact)
  (i j : ι)
  (hij : c.Rel i j) :
-- imply
  hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j = HomologicalComplex.homologyMap φ.τ₃ i ≫ hS₂.δ i j hij :=
-- proof
  HomologicalComplex.HomologySequence.δ_naturality φ hS₁ hS₂ i j hij

/--
[homology_les](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/Thm2350.lean)
-/
@[path]
lemma homology_les
  [Category C]
  [Abelian C]
  {c : ComplexShape ι}
  {S₁ S₂ : ShortComplex (HomologicalComplex C c)}
  {φ : S₁ ⟶ S₂}
  {i j : ι}
-- given
  (hS₁ : S₁.ShortExact)
  (hS₂ : S₂.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (HomologicalComplex.HomologySequence.composableArrows₅ hS₁ i j hij).Exact ∧ (hS₁.δ i j hij ≫ HomologicalComplex.homologyMap φ.τ₁ j = HomologicalComplex.homologyMap φ.τ₃ i ≫ hS₂.δ i j hij) :=
-- proof
  ⟨homology_les_exact hS₁ i j hij,
    homology_les_naturality φ hS₁ hS₂ i j hij⟩


-- created on 2026-10-23
