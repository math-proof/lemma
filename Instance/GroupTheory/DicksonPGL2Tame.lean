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
public import Def.GroupTheory.DicksonPGL2Tame

@[expose] public section

/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/


namespace MetaMathlibExt

open scoped BigOperators

instance dicksonExceptionalAction (G X : Type*) [Group G] [MulAction G X] :
    MulAction G (dicksonExceptional G X) where
  smul g x := ⟨g • x.1, by
    obtain ⟨h, hh, hx⟩ := x.2
    refine ⟨g * h * g⁻¹, ?_, ?_⟩
    · intro heq
      apply hh
      have := congrArg (fun k : G => g⁻¹ * k * g) heq
      simpa [mul_assoc] using this
    · simp [mul_smul, hx]⟩
  one_smul x := Subtype.ext (one_smul G x.1)
  mul_smul g h x := Subtype.ext (mul_smul g h x.1)

end MetaMathlibExt
