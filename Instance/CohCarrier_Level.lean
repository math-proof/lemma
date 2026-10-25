-- Carved from Lemma/Definitions/Def_CohCarrier_Level.lean: instance decls only.
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.GroupTheory.Transfer
import Mathlib.Algebra.Module.Hom
import Mathlib.Data.ZMod.Units
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import Def.CohCarrier_Level

set_option autoImplicit false

open Matrix CongruenceSubgroup Matrix.SpecialLinearGroup

open scoped MatrixGroups

namespace CohCarrier


section Operators

variable (M : ℕ) (H : Subgroup (ZMod M)ˣ) (ℓ : ℕ)

variable (A : Type*) [AddCommGroup A]

instance Gamma0Upper_finiteIndex [NeZero ℓ] : (Gamma0Upper ℓ).FiniteIndex :=
  (Gamma0Upper_isCongruenceSubgroup ℓ).finiteIndex

end Operators

section LevelMaps

variable (M M' : ℕ) (H : Subgroup (ZMod M)ˣ) (H' : Subgroup (ZMod M')ˣ) (d : ℕ)

variable {M M' H H' d}

variable (M M' H H' d)

variable (A : Type*) [AddCommGroup A]

instance iotaDeg_range_finiteIndex [NeZero M'] [NeZero d] (h : LevelLE M M' H H' d) :
    ((iotaDeg M M' H H' d h).range).FiniteIndex := by
  haveI : NeZero (M' * d) := ⟨mul_ne_zero (NeZero.ne M') (NeZero.ne d)⟩
  haveI : ((Gamma (M' * d)).subgroupOf (GammaH M H)).FiniteIndex := inferInstance
  exact Subgroup.finiteIndex_of_le (Gamma_subgroupOf_le_range_iotaDeg M M' H H' d h)

end LevelMaps

end CohCarrier
