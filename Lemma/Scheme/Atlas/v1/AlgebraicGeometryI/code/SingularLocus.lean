import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.AlgebraicGeometryI.code.SingularLocus
open AlgebraicGeometry Algebra


/--
[singularLocus_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SingularLocus.lean)
-/
@[path]
lemma singularLocus_isClosed
  {X : Scheme.{u}}
  {K : Type u}
  [Field K]
  {f : X ⟶ Spec (.of K)}
  [LocallyOfFinitePresentation f] :
-- imply
  IsClosed (singularLocus f) :=
-- proof
  f.isOpen_smoothLocus.isClosed_compl

/--
[singularLocus_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SingularLocus.lean)
-/
@[path]
lemma singularLocus_ne_univ
  {X : Scheme.{u}}
  {K : Type u}
  [Field K]
  [PerfectField K]
  [IsReduced X]
  [Nonempty X]
  {f : X ⟶ Spec (.of K)}
  [LocallyOfFinitePresentation f] :
-- imply
  singularLocus f ≠ Set.univ := by
-- proof
  intro h
  have hempty : (f.smoothLocus : Set X) = ∅ := Set.compl_univ_iff.mp h
  have hd := f.dense_smoothLocus_of_perfectField
  rw [hempty] at hd
  have h1 := hd.closure_eq
  simp at h1
  exact Set.empty_ne_univ h1
variable {A : Type*} [CommRing A] [Algebra K A]

/--
[singularLocusAlg_isClosed](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/SingularLocus.lean)
-/
@[path]
lemma singularLocusAlg_isClosed
  {X : Scheme.{u}}
  {K : Type u}
  [Field K]
  [CommRing A]
  [Algebra K A]
  [FinitePresentation K A] :
-- imply
  IsClosed (singularLocusAlg K A) :=
-- proof
  isOpen_smoothLocus.isClosed_compl


-- created on 2026-10-23
