/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean -/

/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
module

public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.GroupTheory.SemidirectProduct
public import Mathlib.GroupTheory.SpecificGroups.Alternating
public import Mathlib.GroupTheory.SpecificGroups.Dihedral
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Projective
public import Mathlib.LinearAlgebra.Matrix.ProjectiveSpecialLinearGroup
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.GroupTheory.IndexNormal
public import Mathlib.GroupTheory.Rank
public import Mathlib.GroupTheory.Sylow
public import Mathlib.FieldTheory.Separable
public import Mathlib.LinearAlgebra.Eigenspace.Semisimple
public import Mathlib.LinearAlgebra.Projectivization.Action
public import Mathlib.RepresentationTheory.Maschke
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.Simproc.Factors
public import Theorem.Nat.AddCardMul_SubCard1.eq.MulCard_QuotientOrbitRelCard
public import Def.GroupTheory.DicksonPGL2Tame.Part2

/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/

public section


namespace MetaMathlibExt

open scoped BigOperators

namespace Dickson

lemma dickson_normalizedLift_exists {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F))
    (h : MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x) :
    ∃ A : GL (Fin 2) F,
      Matrix.ProjGenLinGroup.mk A = h.1 ∧
      (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) x.rep = x.rep := by
  obtain ⟨A, hA⟩ := Matrix.ProjGenLinGroup.mk_surjective h.1
  have hfix : Matrix.ProjGenLinGroup.mk A • x = x := by
    rw [hA]
    exact h.2
  rw [← Projectivization.mk_rep x, Projectivization.PGL.mk_smul_mk,
    Projectivization.mk_eq_mk_iff] at hfix
  obtain ⟨u, hu⟩ := hfix
  let B := Matrix.GeneralLinearGroup.scalar (Fin 2) u⁻¹ * A
  refine ⟨B, ?_, ?_⟩
  · simp [B, hA]
  · change Matrix.mulVec (B : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep
    simp only [B, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
    rw [← Matrix.mulVec_mulVec]
    have hu' : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) x.rep =
        (u : F) • x.rep := by
      simpa [Units.smul_def, Matrix.smul_eq_mulVec] using hu.symm
    rw [hu']
    ext i
    simp [Matrix.mulVec, Matrix.scalar]

lemma dickson_normalizedLift_unique {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F)) {A B : GL (Fin 2) F}
    (hmk : Matrix.ProjGenLinGroup.mk A = Matrix.ProjGenLinGroup.mk B)
    (hA : (↑(Matrix.GeneralLinearGroup.toLin A) : Module.End F (Fin 2 → F)) x.rep = x.rep)
    (hB : (↑(Matrix.GeneralLinearGroup.toLin B) : Module.End F (Fin 2 → F)) x.rep = x.rep) :
    A = B := by
  obtain ⟨u, hu⟩ := Matrix.ProjGenLinGroup.mk_eq_mk_iff.mp hmk
  have huv : (u : F) • x.rep = x.rep := by
    have hu' : Matrix.GeneralLinearGroup.scalar (Fin 2) u * A = B := by
      rw [Matrix.GeneralLinearGroup.scalar_commute]
      exact hu
    have happ := congrArg (fun C : GL (Fin 2) F =>
      Matrix.mulVec (C : Matrix (Fin 2) (Fin 2) F) x.rep) hu'
    simp only [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] at happ
    rw [← Matrix.mulVec_mulVec] at happ
    have hscalar (w : Fin 2 → F) :
        Matrix.mulVec (Matrix.scalar (Fin 2) (u : F)) w = (u : F) • w := by
      ext i
      simp [Matrix.mulVec, Matrix.scalar]
    have hAm : Matrix.mulVec (A : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep := hA
    have hBm : Matrix.mulVec (B : Matrix (Fin 2) (Fin 2) F) x.rep = x.rep := hB
    rw [hscalar, hAm, hBm] at happ
    exact happ
  have hu1 : (u : F) = 1 := by
    apply smul_left_injective F x.rep_nonzero
    simpa using huv
  have huunit : u = 1 := Units.ext hu1
  subst u
  simpa using hu

end Dickson
end MetaMathlibExt
