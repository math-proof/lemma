import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.v1.Atlas.NumberTheoryI.code.LocalFields.Part9

open scoped Valued
open NumberField NumberField.InfinitePlace.Completion IsDedekindDomain


/--
[isLocalField_iff_closedBalls_compact](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
section DiscreteValuationCharacterization
open scoped Valued

/--
[isLocalField_iff_complete_dvr_finiteResidue](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
end DiscreteValuationCharacterization

/--
[locallyCompact_of_finiteDimensional_over_localField](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
@[reducible] noncomputable def isLocalField_real : IsLocalField ℝ := inferInstance
@[reducible] noncomputable def corollary_9_7_archimedean : IsLocalField ℝ := isLocalField_real
@[reducible] noncomputable def isLocalField_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  instIsLocalFieldPadic p
@[reducible] noncomputable def corollary_9_7_padic (p : ℕ) [Fact (Nat.Prime p)] : IsLocalField ℚ_[p] :=
  isLocalField_padic p
@[reducible] noncomputable def isLocalField_of_finiteDimensional_extension (K : Type*) [IsLocalField K]
  (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
  IsLocalField L where
  locallyCompact := locallyCompact_of_finiteDimensional_over_localField K L
@[reducible] noncomputable def corollary_9_7_finite_extension (K : Type*) [IsLocalField K]
  (L : Type*) [NontriviallyNormedField L] [NormedAlgebra K L] [FiniteDimensional K L] :
  IsLocalField L :=
  isLocalField_of_finiteDimensional_extension K L
@[reducible] noncomputable def localField_Qp (p : ℕ) [Fact (Nat.Prime p)] :
  IsLocalField ℚ_[p] := isLocalField_padic p

/--
[IsLocalField.finiteDimensional_of_locallyCompact_module](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
set_option maxHeartbeats 400000 in

/--
[completion_finiteDimensional_padic](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/NumberTheoryI/code/LocalFields.lean)
-/
