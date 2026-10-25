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
import Theorem.GroupTheory.DicksonPGL2Tame.Part2
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
