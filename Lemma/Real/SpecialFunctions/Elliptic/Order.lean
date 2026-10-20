import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.Elliptic.Order
open PeriodPair


/--
[poleMultiplicity_eq_zero_of_not_meromorphicAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleMultiplicity_eq_zero_of_not_meromorphicAt_eq
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (h : ¬MeromorphicAt f z) :
-- imply
  poleMultiplicity f z = 0 := by
-- proof
  apply PeriodPair.poleMultiplicity_eq_zero_of_not_meromorphicAt h

/--
[poleMultiplicity_eq_zero_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleMultiplicity_eq_zero_of_nonneg_eq
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (h : 0 ≤ meromorphicOrderAt f z) :
-- imply
  poleMultiplicity f z = 0 := by
-- proof
  apply PeriodPair.poleMultiplicity_eq_zero_of_nonneg h

/--
[poleMultiplicity_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleMultiplicity_ne_zero_iff_eq
  {f : ℂ → ℂ}
  {z : ℂ} :
-- imply
  poleMultiplicity f z ≠ 0 ↔ meromorphicOrderAt f z < 0 := by
-- proof
  apply PeriodPair.poleMultiplicity_ne_zero_iff

/--
[poleMultiplicity_eq_neg_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleMultiplicity_eq_neg_divisor_eq
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z : ℂ}
-- given
  (hf : MeromorphicOn f U)
  (hz : z ∈ U) :
-- imply
  poleMultiplicity f z = (-(MeromorphicOn.divisor f U z)).toNat := by
-- proof
  apply PeriodPair.poleMultiplicity_eq_neg_divisor hf hz

/--
[mem_poleSetInFundamentalParallelogram_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma mem_poleSetInFundamentalParallelogram_iff_eq
  {L : PeriodPair}
  {f : ℂ → ℂ}
  {α z : ℂ} :
-- imply
  z ∈ L.poleSetInFundamentalParallelogram f α ↔
    z ∈ L.fundamentalParallelogram α ∧ poleMultiplicity f z ≠ 0 := by
-- proof
  apply PeriodPair.mem_poleSetInFundamentalParallelogram_iff

/--
[isBounded_fundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma isBounded_fundamentalParallelogram_eq
  {L : PeriodPair}
  {α : ℂ} :
-- imply
  Bornology.IsBounded (L.fundamentalParallelogram α) := by
-- proof
  apply PeriodPair.isBounded_fundamentalParallelogram L α

/--
[poleSetInFundamentalParallelogram_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleSetInFundamentalParallelogram_finite_eq
  {L : PeriodPair}
  {f : ℂ → ℂ}
  {α : ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  (L.poleSetInFundamentalParallelogram f α).Finite := by
-- proof
  apply PeriodPair.poleSetInFundamentalParallelogram_finite L hf α

/--
[ellipticOrder_eq_orderInFundamentalParallelogram_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma ellipticOrder_eq_orderInFundamentalParallelogram_zero_eq
  {L : PeriodPair}
  {f : ℂ → ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf := by
-- proof
  apply PeriodPair.ellipticOrder_eq_orderInFundamentalParallelogram_zero L hf

/--
[poleMultiplicity_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
private lemma poleMultiplicity_const_eq
  {c z : ℂ} :
-- imply
  poleMultiplicity (fun _ => c) z = 0 := by
-- proof
  apply PeriodPair.poleMultiplicity_const c z


-- created on 2026-10-20
