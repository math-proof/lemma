/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Wild.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/

import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.GroupTheory.SpecificGroups.Alternating
import Mathlib.GroupTheory.SpecificGroups.Dihedral
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
import Theorem.GroupTheory.DicksonPGL2Tame.Part4
import Lemma.Nat.Card_Stabilizer
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.Algebra.Group.IsCommutative
import Mathlib.Algebra.Module.ZMod
import Mathlib.FieldTheory.Separable
import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SchurZassenhaus
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
/-!
# Dickson's classification in the wild case

This file classifies finite subgroups of `PGL₂` over an algebraic closure of an odd finite
field when the characteristic divides the group order. It also supplies the projective linear
group order formulas and characteristic-order element facts used by the classification.
-/


namespace MetaMathlibExt

namespace Dickson

open scoped BigOperators Pointwise Polynomial

noncomputable def dicksonWild_projectiveSpecialLinearGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjectiveSpecialLinearGroup n R ≃*
      Matrix.ProjectiveSpecialLinearGroup n S := by
  let f := Matrix.SpecialLinearGroup.map (n := n) e.toRingHom
  let g := Matrix.SpecialLinearGroup.map (n := n) e.symm.toRingHom
  have hgf (x : Matrix.SpecialLinearGroup n R) : g (f x) = x := by
    ext i k
    exact e.symm_apply_apply (x i k)
  have hfg (x : Matrix.SpecialLinearGroup n S) : f (g x) = x := by
    ext i k
    exact e.apply_symm_apply (x i k)
  have hfSurj : Function.Surjective f := fun y ↦ ⟨g y, hfg y⟩
  have hgSurj : Function.Surjective g := fun x ↦ ⟨f x, hgf x⟩
  have hfCenter : Subgroup.center (Matrix.SpecialLinearGroup n R) ≤
      Subgroup.comap f (Subgroup.center (Matrix.SpecialLinearGroup n S)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hfSurj y
    simpa only [map_mul] using congrArg f ((Subgroup.mem_center_iff.mp hx) z)
  have hgCenter : Subgroup.center (Matrix.SpecialLinearGroup n S) ≤
      Subgroup.comap g (Subgroup.center (Matrix.SpecialLinearGroup n R)) := by
    intro x hx
    rw [Subgroup.mem_comap, Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := hgSurj y
    simpa only [map_mul] using congrArg g ((Subgroup.mem_center_iff.mp hx) z)
  let qf := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n R))
    (Subgroup.center (Matrix.SpecialLinearGroup n S)) f hfCenter
  let qg := QuotientGroup.map (Subgroup.center (Matrix.SpecialLinearGroup n S))
    (Subgroup.center (Matrix.SpecialLinearGroup n R)) g hgCenter
  have hqgf (x : Matrix.ProjectiveSpecialLinearGroup n R) : qg (qf x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hgf]
  have hqfg (x : Matrix.ProjectiveSpecialLinearGroup n S) : qf (qg x) = x := by
    exact QuotientGroup.induction_on x fun z ↦ by
      rw [QuotientGroup.map_mk, QuotientGroup.map_mk, hfg]
  exact MulEquiv.ofBijective qf ⟨
    fun x y hxy ↦ by rw [← hqgf x, ← hqgf y, hxy],
    fun y ↦ ⟨qg y, hqfg y⟩⟩

noncomputable def dicksonWild_projGenLinGroup_congr
    {n R S : Type*} [Fintype n] [DecidableEq n] [CommRing R] [CommRing S]
    (e : R ≃+* S) :
    Matrix.ProjGenLinGroup n R ≃* Matrix.ProjGenLinGroup n S := by
  let f := Matrix.ProjGenLinGroup.map (n := n) e.toRingHom
  let g := Matrix.ProjGenLinGroup.map (n := n) e.symm.toRingHom
  apply MonoidHom.toMulEquiv f g
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.symm.toRingHom
        (Matrix.GeneralLinearGroup.map e.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.symm_apply_apply (A i k)
    rw [hA]
    rfl
  · apply MonoidHom.ext
    intro x
    obtain ⟨A, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective x
    rw [MonoidHom.comp_apply, Matrix.ProjGenLinGroup.map_mk,
      Matrix.ProjGenLinGroup.map_mk]
    have hA : Matrix.GeneralLinearGroup.map e.toRingHom
        (Matrix.GeneralLinearGroup.map e.symm.toRingHom A) = A := by
      apply Units.ext
      ext i k
      exact e.apply_symm_apply (A i k)
    rw [hA]
    rfl

def dicksonWildExceptional (G X : Type*) [Group G] [MulAction G X] :=
  {x : X // ∃ g : G, g ≠ 1 ∧ g • x = x}

end Dickson
end MetaMathlibExt
