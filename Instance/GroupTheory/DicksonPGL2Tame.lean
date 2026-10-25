/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean -/

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
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Rank
import Mathlib.GroupTheory.Sylow
import Mathlib.FieldTheory.Separable
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Projectivization.Action
import Mathlib.RepresentationTheory.Maschke
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Simproc.Factors
import Lemma.Nat.AddCardMul_SubCard1.eq.MulCard_QuotientOrbitRelCard
import Def.GroupTheory.DicksonPGL2Tame
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
