-- Carved from Lemma/Definitions/Def_Mathlib_MeasureTheory_Group_Action.lean: instance decls only.
import Mathlib

section


open Subgroup Set
open scoped Pointwise

namespace MeasureTheory
variable {G α : Type*} [Group G] [MeasurableSpace G] [MeasurableSpace α]
  {H K : Subgroup G}

@[to_additive]
instance [MeasurableMul₂ G] : MeasurableMul₂ H where
  measurable_mul := Measurable.subtype_mk (by measurability)

@[to_additive]
instance [MeasurableInv G] : MeasurableInv H where
  measurable_inv := Measurable.subtype_mk (by measurability)

variable [MeasurableMul G]

@[to_additive]
instance : MeasurableMul H where
  measurable_mul_const c := Measurable.subtype_mk (by measurability)
  measurable_const_mul c := Measurable.subtype_mk (by measurability)


end MeasureTheory
end
