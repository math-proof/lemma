import Mathlib
import sympy.Basic
import sympy.atlas.Analysis.SpecialFunctions.Elliptic.Order
open PeriodPair


namespace PeriodPair

/--
[poleMultiplicity_eq_zero_of_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleMultiplicity_eq_zero_of_nonneg
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (h : 0 ≤ meromorphicOrderAt f z) :
-- imply
  poleMultiplicity f z = 0 := by
-- proof
  unfold poleMultiplicity
  cases h' : meromorphicOrderAt f z with
  | top => simp
  | coe n =>
    rw [WithTop.untop₀_coe]
    exact Int.toNat_eq_zero.mpr (neg_nonpos.mpr (by exact_mod_cast h' ▸ h))

end PeriodPair

namespace PeriodPair

/--
[mem_poleSetInFundamentalParallelogram_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma mem_poleSetInFundamentalParallelogram_iff
  {L : PeriodPair}
  {f : ℂ → ℂ}
  {α z : ℂ} :
-- imply
  z ∈ L.poleSetInFundamentalParallelogram f α ↔
    z ∈ L.fundamentalParallelogram α ∧ poleMultiplicity f z ≠ 0 :=
-- proof
  Iff.rfl

end PeriodPair

namespace PeriodPair

/--
[ellipticOrder_eq_orderInFundamentalParallelogram_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma ellipticOrder_eq_orderInFundamentalParallelogram_zero
  {L : PeriodPair}
  {f : ℂ → ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  L.ellipticOrder f hf = L.ellipticOrderInFundamentalParallelogram f 0 hf :=
-- proof
  rfl

end PeriodPair

namespace PeriodPair

/--
[poleMultiplicity_const](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleMultiplicity_const
  {c z : ℂ} :
-- imply
  poleMultiplicity (fun _ => c) z = 0 := by
-- proof
  by_cases hc : c = 0
  · subst hc
    simp [poleMultiplicity, meromorphicOrderAt_const]
  · have h : (0 : WithTop ℤ) ≤ meromorphicOrderAt (fun _ => c) z := by
    simp [meromorphicOrderAt_const, hc]
    exact poleMultiplicity_eq_zero_of_nonneg h

end PeriodPair

/--
[poleMultiplicity_eq_zero_of_not_meromorphicAt](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleMultiplicity_eq_zero_of_not_meromorphicAt
  {f : ℂ → ℂ}
  {z : ℂ}
-- given
  (h : ¬MeromorphicAt f z) :
-- imply
  poleMultiplicity f z = 0 := by
-- proof
  rw [poleMultiplicity, meromorphicOrderAt_of_not_meromorphicAt h]
  rfl


namespace PeriodPair

/--
[poleMultiplicity_ne_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleMultiplicity_ne_zero_iff
  {f : ℂ → ℂ}
  {z : ℂ} :
-- imply
  poleMultiplicity f z ≠ 0 ↔ meromorphicOrderAt f z < 0 := by
-- proof
  constructor
  · intro hne
    by_contra hge
    push Not at hge
    exact hne (poleMultiplicity_eq_zero_of_nonneg hge)
  · intro hlt hcon
    unfold poleMultiplicity at hcon
    rw [Int.toNat_eq_zero] at hcon
    have hle : (0 : ℤ) ≤ (meromorphicOrderAt f z).untop₀ := neg_nonpos.mp hcon
    have htop : meromorphicOrderAt f z ≠ ⊤ := ne_top_of_lt hlt
    have hcoe : ((meromorphicOrderAt f z).untop₀ : WithTop ℤ) =
      meromorphicOrderAt f z :=
      WithTop.coe_untop₀_of_ne_top htop
    have hle' : (0 : WithTop ℤ) ≤ meromorphicOrderAt f z :=
      hcoe ▸ (by exact_mod_cast hle)
    exact not_lt_of_ge hle' hlt

end PeriodPair

namespace PeriodPair

/--
[poleMultiplicity_eq_neg_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleMultiplicity_eq_neg_divisor
  {f : ℂ → ℂ}
  {U : Set ℂ}
  {z : ℂ}
-- given
  (hf : MeromorphicOn f U)
  (hz : z ∈ U) :
-- imply
  poleMultiplicity f z = (-(MeromorphicOn.divisor f U z)).toNat := by
-- proof
  rw [hf.divisor_apply hz]
  rfl

end PeriodPair

namespace PeriodPair

/--
[isBounded_fundamentalParallelogram](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma isBounded_fundamentalParallelogram
  {L : PeriodPair}
  {α : ℂ} :
-- imply
  Bornology.IsBounded (L.fundamentalParallelogram α) := by
-- proof
  have hsub : L.fundamentalParallelogram α ⊆
    (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) ''
      (Set.Icc (0 : ℝ) 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    intro z hz
    rw [mem_fundamentalParallelogram_iff] at hz
    obtain ⟨t₁, t₂, h1, h2, h3, h4, rfl⟩ := hz
    exact ⟨(t₁, t₂),
      ⟨Set.mem_Icc.mpr ⟨h1, le_of_lt h2⟩, Set.mem_Icc.mpr ⟨h3, le_of_lt h4⟩⟩,
      rfl⟩
  have hcont : Continuous (fun p : ℝ × ℝ => α + p.1 • L.ω₁ + p.2 • L.ω₂) := by
    fun_prop
  exact (isCompact_Icc.prod isCompact_Icc |>.image hcont).isBounded.subset hsub

end PeriodPair

namespace PeriodPair

/--
[poleSetInFundamentalParallelogram_finite](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Analysis/SpecialFunctions/Elliptic/Order.lean)
-/
@[path]
lemma poleSetInFundamentalParallelogram_finite
  {L : PeriodPair}
  {f : ℂ → ℂ}
  {α : ℂ}
-- given
  (hf : L.IsEllipticFunction f) :
-- imply
  (L.poleSetInFundamentalParallelogram f α).Finite := by
-- proof
  obtain ⟨R, hR⟩ := (L.isBounded_fundamentalParallelogram α).subset_closedBall 0
  have hU : MeromorphicOn f (Metric.closedBall 0 R) := hf.meromorphic.meromorphicOn
  have hfin := hU.divisor_support_finite_of_subset (isCompact_closedBall 0 R) hR
  refine hfin.subset ?_
  intro z hz
  rw [mem_poleSetInFundamentalParallelogram_iff] at hz
  obtain ⟨hzFP, hmult⟩ := hz
  have hlt : meromorphicOrderAt f z < 0 := poleMultiplicity_ne_zero_iff.mp hmult
  rw [Function.mem_support]
  rw [MeromorphicOn.divisor_apply (hU.mono_set hR) hzFP]
  intro hcon
  rw [WithTop.untop₀_eq_zero] at hcon
  obtain h0 | htop' := hcon
  · rw [h0] at hlt
    exact lt_irrefl _ hlt
  · rw [htop'] at hlt
    exact not_top_lt hlt

end PeriodPair


-- created on 2026-10-20
-- updated on 2026-10-23
