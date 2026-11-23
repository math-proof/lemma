-- Carved from Lemma/Definitions/Def_ProjectiveLineMatrixAction.lean: instance decls only.
import Mathlib
import Instance.ModularCurve_ProjectiveLine
import Theorem.Matrix.ProjectiveLineMatrixAction
import Def.Matrix_ProjectiveLineMatrixAction


namespace HeckeEis

open ModularCurve
open scoped MatrixGroups


instance instFiniteProjLineCusps (N : ℕ) [NeZero N] : Finite (ProjLineCusps N) :=
  Quotient.finite _

end HeckeEis
