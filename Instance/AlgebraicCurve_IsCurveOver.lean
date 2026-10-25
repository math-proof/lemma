-- Carved from Lemma/Definitions/Def_AlgebraicCurve_IsCurveOver.lean: instance decls only.
import Class.AlgebraicCurve_IsCurveOver
import Mathlib.FieldTheory.IsAlgClosed.Basic

set_option autoImplicit false

noncomputable section

open KaehlerDifferential

namespace AlgebraicCurve

variable (K F : Type*) [Field K] [Field F] [Algebra K F]


namespace IsCurveOver

variable {K F}


instance instFiniteResidue [IsCurveOver K F] (v : Place K F) : v.FiniteResidue :=
  ⟨IsCurveOver.finiteResidue v⟩

instance instFreeKaehler [h : IsCurveOver K F] : Module.Free F Ω[F⁄K] :=
  h.kaehler_free_rank_one.1


instance instNontrivialKaehler [h : IsCurveOver K F] : Nontrivial Ω[F⁄K] :=
  Module.nontrivial_of_finrank_eq_succ (n := 0) h.kaehler_free_rank_one.2

end IsCurveOver


end AlgebraicCurve
