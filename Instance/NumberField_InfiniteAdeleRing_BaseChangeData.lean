-- Carved from Lemma/Definitions/Def_NumberField_InfiniteAdeleRing_BaseChangeData.lean: instance decls only.
import Mathlib
import Class.NumberField_Extension

open NumberField TensorProduct

open scoped TensorProduct

namespace FLT.InfiniteAdeleBaseChange

noncomputable section

variable (K L : Type*) [Field K] [Field L] [Algebra K L]

variable {K L}


variable (K L)

variable {K L}

section SelfExtension

variable (K)

instance uniqueSelfExtension (v : InfinitePlace K) : Unique (v.Extension K) where
  default := ⟨v, rfl⟩
  uniq w := Subtype.ext w.property

end SelfExtension


end

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_one_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.conorm_algebraMap' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeRingEquiv_tmul_one' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeAlgEquiv' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.InfinitePlaceData.baseChangeAlgEquiv_one_tmul' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.tensorPiAlgHom_bijective' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.collapsePlaces' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.BaseChangeData.ofInfinitePlaceData' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.selfInfinitePlaceData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.selfBaseChangeData' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_baseChangeRingEquiv_separates' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_conorm_self_fixes_principal' depends on axioms: [propext,
 Classical.choice,
 Quot.sound]
-/

/--
info: 'FLT.InfiniteAdeleBaseChange.gate_conorm_separates' depends on axioms: [propext, Classical.choice, Quot.sound]
-/

end FLT.InfiniteAdeleBaseChange
