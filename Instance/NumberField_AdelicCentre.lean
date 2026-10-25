-- Carved from Lemma/Definitions/Def_NumberField_AdelicCentre.lean: instance decls only.
import Instance.NumberField_AdelicHaar
import Lemma.NumberField.AdelicCentre
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic

open IsDedekindDomain NumberField MeasureTheory
open scoped Pointwise

noncomputable section

namespace NumberField.AdelicCentre

variable (R K : Type*) [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
  [IsFractionRing R K]


section NumberFieldCase

variable [Module.Free ℤ R] [Module.Finite ℤ R] [NumberField K]

instance isClosed_center :
    IsClosed ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K)))) := by
  have : ((Subgroup.center (GL (Fin 2) (AdeleRing R K)) : Set (GL (Fin 2) (AdeleRing R K))))
      = ⋂ g : GL (Fin 2) (AdeleRing R K), {z | g * z = z * g} := by
    ext z
    simp only [SetLike.mem_coe, Subgroup.mem_center_iff, Set.mem_iInter, Set.mem_setOf_eq]
  rw [this]
  exact isClosed_iInter fun g =>
    isClosed_eq (continuous_const.mul continuous_id) (continuous_id.mul continuous_const)

instance t2Space_adelicPGL2 : T2Space (AdelicPGL2 R K) := inferInstance

instance locallyCompactSpace_adelicPGL2 : LocallyCompactSpace (AdelicPGL2 R K) := inferInstance

instance isTopologicalGroup_adelicPGL2 : IsTopologicalGroup (AdelicPGL2 R K) := inferInstance


end NumberFieldCase

end NumberField.AdelicCentre

end
