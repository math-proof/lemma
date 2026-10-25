import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.LongExactSequence
open CategoryTheory CategoryTheory.Limits HomologicalComplex LongExactSequence


namespace LongExactSequence

/--
[long_exact_sequence_exact_at_Hi_B](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma long_exact_sequence_exact_at_Hi_B
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i : ι}
-- given
  (hS : S.ShortExact) :
-- imply
  (ShortComplex.mk (homologyMap S.f i) (homologyMap S.g i) (by rw [← homologyMap_comp, S.zero, homologyMap_zero])).Exact :=
-- proof
  hS.homology_exact₂ i

end LongExactSequence

namespace LongExactSequence

/--
[long_exact_sequence_exact_at_Hi_C](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma long_exact_sequence_exact_at_Hi_C
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact :=
-- proof
  hS.homology_exact₃ i j hij

end LongExactSequence

namespace LongExactSequence

/--
[long_exact_sequence_exact_at_Hj_A](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma long_exact_sequence_exact_at_Hj_A
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
-- proof
  hS.homology_exact₁ i j hij

end LongExactSequence

namespace LongExactSequence

/--
[long_exact_sequence](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma long_exact_sequence
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j) :
-- imply
  (ShortComplex.mk (homologyMap S.f i) (homologyMap S.g i) (by rw [← homologyMap_comp, S.zero, homologyMap_zero])).Exact ∧ (ShortComplex.mk _ _ (hS.comp_δ i j hij)).Exact ∧ (ShortComplex.mk _ _ (hS.δ_comp i j hij)).Exact :=
-- proof
  ⟨hS.homology_exact₂ i, hS.homology_exact₃ i j hij, hS.homology_exact₁ i j hij⟩

end LongExactSequence

namespace LongExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
/--
[mono_cohomologyδ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma mono_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
  (hi : IsZero (S.X₂.homology i)) : Mono (cohomologyδ hS i j hij) :=
  hS.mono_δ i j hij hi

end LongExactSequence

namespace LongExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
/--
[epi_cohomologyδ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma epi_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
  (hj : IsZero (S.X₂.homology j)) : Epi (cohomologyδ hS i j hij) :=
  hS.epi_δ i j hij hj

end LongExactSequence

namespace LongExactSequence

variable {C : Type u} [Category.{v} C] [Abelian C] {ι : Type*} {c : ComplexShape ι} {S : ShortComplex (HomologicalComplex C c)}
/--
[isIso_cohomologyδ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
lemma isIso_cohomologyδ (hS : S.ShortExact) (i j : ι) (hij : c.Rel i j)
  (hi : IsZero (S.X₂.homology i)) (hj : IsZero (S.X₂.homology j)) :
  IsIso (cohomologyδ hS i j hij) :=
  hS.isIso_δ i j hij hi hj

end LongExactSequence

/--
[mono_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
private lemma mono_cohomology_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j)
  (hi : IsZero (S.X₂.homology i)) :
-- imply
  Mono (cohomologyδ hS i j hij) := by
-- proof
  apply LongExactSequence.mono_cohomology hS i j hij hi

/--
[epi_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
private lemma epi_cohomology_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j)
  (hj : IsZero (S.X₂.homology j)) :
-- imply
  Epi (cohomologyδ hS i j hij) := by
-- proof
  apply LongExactSequence.epi_cohomology hS i j hij hj

/--
[isIso_cohomology](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/LongExactSequence.lean)
-/
@[path]
private lemma isIso_cohomology_eq
  {C : Type u}
  [Category.{v} C]
  [Abelian C]
  {i j : ι}
-- given
  (hS : S.ShortExact)
  (hij : c.Rel i j)
  (hi : IsZero (S.X₂.homology i))
  (hj : IsZero (S.X₂.homology j)) :
-- imply
  IsIso (cohomologyδ hS i j hij) := by
-- proof
  apply LongExactSequence.isIso_cohomology hS i j hij hi hj


-- created on 2026-10-23
