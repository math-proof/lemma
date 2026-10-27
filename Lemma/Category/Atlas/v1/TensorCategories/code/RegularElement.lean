import Mathlib
import Initialize.Tactic.Attr.Basic
import Structure.v1.Atlas.TensorCategories.code.RegularElement
open Finset FusionRing


namespace FusionRing

/--
[RegularElement.isRegularElement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean)
-/
@[path]
lemma RegularElement.isRegularElement
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {fpd : R.FPdimData}
  {reg : R.RegularElement fpd} :
-- imply
  R.IsRegularElement fpd reg.r :=
-- proof
  reg.left_absorb

end FusionRing

namespace FusionRing

/--
[IsRegularElement.coeffs_pos_of_regularElement](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean)
-/
@[path]
lemma IsRegularElement.coeffs_pos_of_regularElement
  [DecidableEq ι]
  [Fintype ι]
  {R : FusionRing ι}
  {fpd : R.FPdimData}
  {reg : R.RegularElement fpd} :
-- imply
  ∀ i, 0 < reg.r i :=
-- proof
  reg.r_pos

end FusionRing

namespace FusionRing

/--
[proposition_1_45_8](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/TensorCategories/code/RegularElement.lean)
-/
@[path]
lemma proposition_1_45_8
  [DecidableEq ι]
  [Fintype ι]
  {A : FusionRing ι}
  {fpd : A.FPdimData}
  {star : ι → ι}
  {X : ι}
-- given
  (hstar : A.IsAntiAutomorphism star) :
-- imply
  fpd.d (star X) = fpd.d X :=
-- proof
  fpd.fpdim_antiAut_invariant star hstar X

end FusionRing


-- created on 2026-10-23
