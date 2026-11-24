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
public import Theorem.GroupTheory.DicksonPGL2Tame.Part2


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

noncomputable def dickson_normalizedLift {F : Type*} [Field F]
    (x : Projectivization F (Fin 2 → F)) :
    MulAction.stabilizer (Matrix.ProjGenLinGroup (Fin 2) F) x →* GL (Fin 2) F where
  toFun := dickson_normalizedLiftFun x
  map_one' := by
    apply dickson_normalizedLift_unique x
    · simp [dickson_normalizedLiftFun_mk]
    · exact dickson_normalizedLiftFun_rep x 1
    · simp
  map_mul' h k := by
    apply dickson_normalizedLift_unique x
    · simp [dickson_normalizedLiftFun_mk]
    · exact dickson_normalizedLiftFun_rep x (h * k)
    · change (↑(Matrix.GeneralLinearGroup.toLin
          (dickson_normalizedLiftFun x h * dickson_normalizedLiftFun x k)) :
          Module.End F (Fin 2 → F)) x.rep = x.rep
      rw [map_mul]
      change (↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLiftFun x h)) :
          Module.End F (Fin 2 → F))
        ((↑(Matrix.GeneralLinearGroup.toLin (dickson_normalizedLiftFun x k)) :
          Module.End F (Fin 2 → F)) x.rep) = x.rep
      rw [dickson_normalizedLiftFun_rep, dickson_normalizedLiftFun_rep]

end Dickson
end MetaMathlibExt
