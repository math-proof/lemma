-- Carved from Lemma/Definitions/Def_Gamma0HeckeOperatorHom.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Index
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Lemma.Gamma0HeckeOperatorHom.Main

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
