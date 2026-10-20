/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/ModifiedBesselFirstKind.lean -/

import Mathlib.Analysis.SpecificLimits.Basic

open scoped BigOperators

namespace MetaMathlibExt

/-- kth term of the modified Bessel function of the first kind series
(concept `jis_sem_78bf9131cc4a7a0691426bd9`, clause `term`;
source statements `jis_3a038c4cc84dc07fe8919282`, `jis_7cc9c1f18e5df469ed601556`,
`jis_e0a513b24ce72583486f4f92`, `jis_f7e9efe0d7b39afbda3962c6`). -/
noncomputable def modifiedBesselI_term (m k : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * k + m) /
    ((2 : ℝ) ^ (2 * k + m) * (Nat.factorial k : ℝ) * (Nat.factorial (k + m) : ℝ))

/-- Modified Bessel function of the first kind `I_m(x)` as the `tsum` series
over `k` of the kth term (concept `jis_sem_78bf9131cc4a7a0691426bd9`,
clause `definition`; source statements `jis_3a038c4cc84dc07fe8919282`,
`jis_7cc9c1f18e5df469ed601556`, `jis_e0a513b24ce72583486f4f92`,
`jis_f7e9efe0d7b39afbda3962c6`). -/
noncomputable def modifiedBesselI (m : ℕ) (x : ℝ) : ℝ :=
  ∑' k : ℕ, modifiedBesselI_term m k x

/-- Order-zero specialization `I_0` (concept `jis_sem_78bf9131cc4a7a0691426bd9`,
clause `zero_order`; source statements `jis_3a038c4cc84dc07fe8919282`,
`jis_7cc9c1f18e5df469ed601556`, `jis_e0a513b24ce72583486f4f92`,
`jis_f7e9efe0d7b39afbda3962c6`). -/
noncomputable def modifiedBesselI_zero (x : ℝ) : ℝ :=
  modifiedBesselI 0 x

/-- Order-one specialization `I_1` (concept `jis_sem_78bf9131cc4a7a0691426bd9`,
clause `one_order`; source statements `jis_3a038c4cc84dc07fe8919282`,
`jis_7cc9c1f18e5df469ed601556`, `jis_e0a513b24ce72583486f4f92`,
`jis_f7e9efe0d7b39afbda3962c6`). -/
noncomputable def modifiedBesselI_one (x : ℝ) : ℝ :=
  modifiedBesselI 1 x

end MetaMathlibExt
