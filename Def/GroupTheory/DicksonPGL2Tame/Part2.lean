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
public import Instance.GroupTheory.DicksonPGL2Tame

@[expose] public section

/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/


namespace MetaMathlibExt

open scoped BigOperators

def dickson_fixedByExceptionalEquiv {G X : Type*} [Group G] [MulAction G X]
    (g : G) (hg : g ≠ 1) :
    MulAction.fixedBy (dicksonExceptional G X) g ≃ MulAction.fixedBy X g where
  toFun x := ⟨x.1.1, congrArg Subtype.val x.2⟩
  invFun x := ⟨⟨x.1, ⟨g, hg, x.2⟩⟩, Subtype.ext x.2⟩
  left_inv x := by ext; rfl
  right_inv x := by ext; rfl

end MetaMathlibExt
