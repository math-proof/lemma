-- Carved from Lemma/Definitions/Def_M4aHerbrand_ArchSemilocal.lean: instance decls only.
import Instance.NumberField_InfiniteAdeleRing_BaseChangeData

namespace M4aHerbrand.ArchSemilocal

open NumberField NumberField.InfinitePlace TensorProduct

open scoped NumberField.LiesOver

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

omit [NumberField K] [NumberField L] in
instance instIsScalarTowerCompletion (w : InfinitePlace L) : IsScalarTower K L w.Completion :=
  .of_algebraMap_eq fun _ => rfl


end

end M4aHerbrand.ArchSemilocal
