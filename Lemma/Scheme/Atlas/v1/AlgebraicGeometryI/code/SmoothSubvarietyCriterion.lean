import Mathlib
import sympy.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SmoothSubvarietyCriterion
open KaehlerDifferential Algebra
open scoped TensorProduct


/--
[smooth_subvariety_criterion_formallySmooth](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothSubvarietyCriterion.lean)
-/
@[path]
lemma smooth_subvariety_criterion_formallySmooth
  {R : Type u}
  {A : Type v}
  {B : Type w}
  [FormallySmooth R A]
-- given
  (hf : Function.Surjective (algebraMap A B)) :
-- imply
  FormallySmooth R B ↔ HasLinearlyIndependentDifferentials R A B :=
-- proof
  FormallySmooth.iff_split_injection hf

/--
[smooth_subvariety_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SmoothSubvarietyCriterion.lean)
-/
@[path]
lemma smooth_subvariety_criterion
  {R : Type u}
  {A : Type v}
  {B : Type w}
  [Smooth R A]
-- given
  (hf : Function.Surjective (algebraMap A B))
  (hker : (RingHom.ker (algebraMap A B)).FG) :
-- imply
  Smooth R B ↔ HasLinearlyIndependentDifferentials R A B := by
-- proof
  constructor
  ·
    intro hB
    haveI : FormallySmooth R B := Smooth.formallySmooth
    exact (FormallySmooth.iff_split_injection hf).mp inferInstance
  ·
    intro h
    haveI : FormallySmooth R A := Smooth.formallySmooth
    haveI : FormallySmooth R B := (FormallySmooth.iff_split_injection hf).mpr h
    haveI : FinitePresentation R A := Smooth.finitePresentation
    haveI : FinitePresentation R B :=
      FinitePresentation.of_surjective (f := IsScalarTower.toAlgHom R A B) hf hker
    exact ⟨inferInstance, inferInstance⟩


-- created on 2026-10-23
