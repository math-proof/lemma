module
public import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
public import Mathlib.GroupTheory.Index
public import Mathlib.GroupTheory.GroupAction.Quotient
public import Mathlib.Tactic.Group
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Tactic.FinCases
public import Theorem.Matrix.Gamma0HeckeOperatorHom
public import Def.Matrix_Gamma0HeckeOperatorHom


public section

-- Carved from Lemma/Definitions/Def_Gamma0HeckeOperatorHom.lean: instance decls only.

namespace HeckeEis

open CongruenceSubgroup Subgroup Matrix
open scoped MatrixGroups


section HeckeSubgroup

variable (N ℓ : ℕ)

instance instFiniteIndexHeckeUpper [NeZero ℓ] : (heckeUpper N ℓ).FiniteIndex :=
  haveI : (gammaZeroRed N ℓ).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  Subgroup.finiteIndex_of_le (ker_gammaZeroRed_le_heckeUpper N ℓ)

variable [NeZero ℓ]

end HeckeSubgroup


end HeckeEis
