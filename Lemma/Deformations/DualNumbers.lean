import Mathlib
import Class.Deformations_ProartinianCat
import Def.Deformations_DualNumbers

set_option autoImplicit false

universe u

open CategoryTheory IsLocalRing TrivSqZeroExt
open scoped DualNumber

namespace Deformation

local notation3:max "𝓴" 𝓞:max => (IsLocalRing.ResidueField 𝓞)

namespace ProartinianCat

variable (𝓞 : Type u) [CommRing 𝓞] [IsLocalRing 𝓞]


lemma residue_inl_fst_eq (y : (𝓴 𝓞)[ε]) :
    residue ((𝓴 𝓞)[ε]) (TrivSqZeroExt.inl y.fst) = residue ((𝓴 𝓞)[ε]) y := by
  refine Ideal.Quotient.eq.mpr ?_
  have h3 : TrivSqZeroExt.inl y.fst - y = -TrivSqZeroExt.inr y.snd := by
    ext <;> simp
  rw [h3]
  refine neg_mem (IsLocalRing.mem_maximalIdeal _ |>.mpr ?_)
  rw [mem_nonunits_iff, TrivSqZeroExt.isUnit_inr_iff]
  exact fun h => (not_subsingleton (𝓴 𝓞)) h


lemma eq_dualNumbersFst (f : dualNumbers 𝓞 ⟶ residueField) : f = dualNumbersFst 𝓞 :=
  Subsingleton.elim _ _

end ProartinianCat

end Deformation
