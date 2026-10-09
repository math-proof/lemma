import Mathlib
import sympy.Basic
import sympy.Analysis.Convex.NewtonPolygon

open Convex.NewtonPolygon Set

/-- [mem_newtonSupport](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma mem_newtonSupport_eq
-- given
  {k : Type*} [CommSemiring k]
  {f : MvPolynomial (Fin 2) k}
  {x : Fin 2 → Real} :
-- imply
  x ∈ newtonSupport f ↔ ∃ e ∈ f.support, exponentToReal e = x := by
-- proof
  apply mem_newtonSupport

/-- [newtonSupport_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma newtonSupport_zero_eq
-- given
  {k : Type*} [CommSemiring k] :
-- imply
  newtonSupport (0 : MvPolynomial (Fin 2) k) = ∅ := by
-- proof
  apply newtonSupport_zero

/-- [newtonPolygon_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma newtonPolygon_zero_eq
-- given
  {k : Type*} [CommSemiring k] :
-- imply
  newtonPolygon (0 : MvPolynomial (Fin 2) k) = ∅ := by
-- proof
  apply newtonPolygon_zero

/-- [newtonSupport_subset_newtonPolygon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma newtonSupport_subset_newtonPolygon_eq
-- given
  {k : Type*} [CommSemiring k]
  (f : MvPolynomial (Fin 2) k) :
-- imply
  newtonSupport f ⊆ newtonPolygon f := by
-- proof
  apply newtonSupport_subset_newtonPolygon f

/-- [newtonPolygonInterior_subset_newtonPolygon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma newtonPolygonInterior_subset_newtonPolygon_eq
-- given
  {k : Type*} [CommSemiring k]
  (f : MvPolynomial (Fin 2) k) :
-- imply
  newtonPolygonInterior f ⊆ newtonPolygon f := by
-- proof
  apply newtonPolygonInterior_subset_newtonPolygon f

/-- [edgeRestriction_empty](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma edgeRestriction_empty_eq
-- given
  {k : Type*} [CommSemiring k]
  (f : MvPolynomial (Fin 2) k) :
-- imply
  edgeRestriction f ∅ = 0 := by
-- proof
  apply edgeRestriction_empty f

/-- [edgeRestriction_univ](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/Convex/NewtonPolygon.lean) -/
@[path]
private lemma edgeRestriction_univ_eq
-- given
  {k : Type*} [CommSemiring k]
  (f : MvPolynomial (Fin 2) k) :
-- imply
  edgeRestriction f Set.univ = f := by
-- proof
  apply edgeRestriction_univ f

-- created on 2026-10-10
