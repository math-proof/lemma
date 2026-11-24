module
public import Mathlib
public import Instance.ModularCurve_ProjectiveLine
public import Theorem.Matrix.ProjectiveLineMatrixAction
public import Def.Matrix_ProjectiveLineMatrixAction


public section

-- Carved from Lemma/Definitions/Def_ProjectiveLineMatrixAction.lean: instance decls only.

namespace HeckeEis

open ModularCurve
open scoped MatrixGroups


instance instFiniteProjLineCusps (N : ℕ) [NeZero N] : Finite (ProjLineCusps N) :=
  Quotient.finite _

end HeckeEis
