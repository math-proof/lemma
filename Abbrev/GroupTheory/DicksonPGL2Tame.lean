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
public import Theorem.GroupTheory.DicksonPGL2Tame.Part3


public section

/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/GroupTheory/DicksonPGL2Tame.lean -/
/-
Authors: Adam Kiezun, Muse Spark 1.3, Codex
-/
/-!
# Tame finite subgroups of `PGL₂`

This file classifies finite subgroups of `PGL₂` whose order is prime to the
characteristic, using the action on the projective line.
-/
namespace MetaMathlibExt

open scoped BigOperators

namespace Dickson

variable (p : ℕ) [Fact (Nat.Prime p)]

/-- An algebraic closure `K p` of the finite field `𝔽_p = ZMod p`. -/
noncomputable abbrev K : Type := AlgebraicClosure (ZMod p)

/-- The projective general linear group `PGL₂(K p)`. -/
abbrev PGL : Type := Matrix.ProjGenLinGroup (Fin 2) (K p)

/-- The projective special linear group `PSL₂(K p)`. -/
abbrev PSL : Type := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (K p)

end Dickson
end MetaMathlibExt
