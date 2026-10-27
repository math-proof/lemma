import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Probability.EntropySubadd.Part2
open Finset Real StatMech StatMech.Probability


/--
[esd_Phi_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_Phi_zero_eq :
-- imply
  esd_Phi 0 = 0 := by
-- proof
  apply StatMech.Probability.esd_Phi_zero

/--
[esd_Phi_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_Phi_eq_eq
  {x : ℝ} :
-- imply
  esd_Phi x = x * Real.log x := by
-- proof
  apply StatMech.Probability.esd_Phi_eq x

/--
[esd_logSum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_logSum_eq
  {t : Finset ι}
  {a b : ι → ℝ}
-- given
  (ha : ∀ i ∈ t, 0 ≤ a i)
  (hb : ∀ i ∈ t, 0 < b i)
  (hA : 0 < ∑ i ∈ t, a i) :
-- imply
  (∑ i ∈ t, a i) * Real.log ((∑ i ∈ t, a i) / (∑ i ∈ t, b i)) ≤ ∑ i ∈ t, a i * Real.log (a i / b i) := by
-- proof
  apply StatMech.Probability.esd_logSum t a b ha hb hA

/--
[esd_bernoulli_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_bernoulli_pos_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1) :
-- imply
  esd_PosWeight (E := E) (OSSS.bernoulliWeight p) := by
-- proof
  apply StatMech.Probability.esd_bernoulli_pos hp0 hp1

/--
[esd_eq_zero_of_expect_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_eq_zero_of_expect_zero_eq
  [Fintype E]
  [DecidableEq E]
  {ν : E → Bool → ℝ}
  {g : ConfigSpace E → ℝ}
-- given
  (hpos : esd_PosWeight ν)
  (hg : ∀ ω, 0 ≤ g ω)
  (h0 : OSSS.expect ν g = 0) :
-- imply
  ∀ ω, g ω = 0 := by
-- proof
  apply StatMech.Probability.esd_eq_zero_of_expect_zero hpos hg h0

/--
[esd_dpi_fiber](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_dpi_fiber_eq
  [Fintype E]
  [DecidableEq E]
  {c0 c1 a0 a1 M0 M1 : ℝ}
-- given
  (hc0 : 0 < c0)
  (hc1 : 0 < c1)
  (ha0 : 0 ≤ a0)
  (ha1 : 0 ≤ a1)
  (hM0 : 0 < M0)
  (hM1 : 0 < M1) :
-- imply
  (c0*a0+c1*a1) * (Real.log (c0*a0+c1*a1) - Real.log (c0*M0+c1*M1)) ≤ c0 * a0 * (Real.log a0 - Real.log M0) + c1 * a1 * (Real.log a1 - Real.log M1) := by
-- proof
  apply StatMech.Probability.esd_dpi_fiber c0 c1 a0 a1 M0 M1 hc0 hc1 ha0 ha1 hM0 hM1

/--
[esd_dpi_fiber_Phi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_dpi_fiber_Phi_eq
  [Fintype E]
  [DecidableEq E]
  {c0 c1 a0 a1 M0 M1 : ℝ}
-- given
  (hc0 : 0 < c0)
  (hc1 : 0 < c1)
  (ha0 : 0 ≤ a0)
  (ha1 : 0 ≤ a1)
  (hM0 : 0 < M0)
  (hM1 : 0 < M1) :
-- imply
  esd_Phi (c0*a0+c1*a1) - (c0*a0+c1*a1) * Real.log (c0*M0+c1*M1) ≤ (c0 * esd_Phi a0 + c1 * esd_Phi a1) - (c0 * a0 * Real.log M0 + c1 * a1 * Real.log M1) := by
-- proof
  apply StatMech.Probability.esd_dpi_fiber_Phi c0 c1 a0 a1 M0 M1 hc0 hc1 ha0 ha1 hM0 hM1

/--
[esd_Phi_scale](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_Phi_scale_eq
  [Fintype E]
  [DecidableEq E]
  {p x : ℝ}
-- given
  (hp : 0 < p)
  (hx : 0 ≤ x) :
-- imply
  p * esd_Phi x - esd_Phi (p * x) = - (p * x) * Real.log p := by
-- proof
  apply StatMech.Probability.esd_Phi_scale p x hp hx

/--
[esd_dpi](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_dpi_eq
  [Fintype E]
  [DecidableEq E]
  {μ : E → Bool → ℝ}
  {p : ℝ}
  {g0 g1 : ConfigSpace E → ℝ}
-- given
  (hpos : esd_PosWeight μ)
  (hprob : OSSS.IsProbWeight μ)
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hg0 : ∀ ω, 0 ≤ g0 ω)
  (hg1 : ∀ ω, 0 ≤ g1 ω) :
-- imply
  p * esd_Phi (OSSS.expect μ g1) + (1-p) * esd_Phi (OSSS.expect μ g0) - esd_Phi (p * OSSS.expect μ g1 + (1-p) * OSSS.expect μ g0) ≤ OSSS.expect μ (fun ω => p * esd_Phi (g1 ω) + (1-p) * esd_Phi (g0 ω) - esd_Phi (p * g1 ω + (1-p) * g0 ω)) := by
-- proof
  apply StatMech.Probability.esd_dpi hpos hprob hp0 hp1 hg0 hg1

/--
[esd_setOpen_succ_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_setOpen_succ_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {e' : Fin n}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  StatMech.setOpen (Fin.succ e') (Fin.cons b ω') = Fin.cons b (StatMech.setOpen e' ω') := by
-- proof
  apply StatMech.Probability.esd_setOpen_succ_cons e' b ω'

/--
[esd_setClosed_succ_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_setClosed_succ_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {e' : Fin n}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  StatMech.setClosed (Fin.succ e') (Fin.cons b ω') = Fin.cons b (StatMech.setClosed e' ω') := by
-- proof
  apply StatMech.Probability.esd_setClosed_succ_cons e' b ω'

/--
[esd_setOpen_zero_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_setOpen_zero_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  StatMech.setOpen 0 (Fin.cons b ω') = Fin.cons true ω' := by
-- proof
  apply StatMech.Probability.esd_setOpen_zero_cons b ω'

/--
[esd_setClosed_zero_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_setClosed_zero_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  StatMech.setClosed 0 (Fin.cons b ω') = Fin.cons false ω' := by
-- proof
  apply StatMech.Probability.esd_setClosed_zero_cons b ω'

/--
[esd_entCoord_succ_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_entCoord_succ_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin (n+1) → Bool) → ℝ}
  {e' : Fin n}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  esd_entCoord p g (Fin.succ e') (Fin.cons b ω') = esd_entCoord p (fun ω' => g (Fin.cons b ω')) e' ω' := by
-- proof
  apply StatMech.Probability.esd_entCoord_succ_cons p g e' b ω'

/--
[esd_entCoord_zero_cons](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_entCoord_zero_cons_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin (n+1) → Bool) → ℝ}
  {b : Bool}
  {ω' : Fin n → Bool} :
-- imply
  esd_entCoord p g 0 (Fin.cons b ω') = p * esd_Phi (g (Fin.cons true ω')) + (1-p) * esd_Phi (g (Fin.cons false ω')) - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω')) := by
-- proof
  apply StatMech.Probability.esd_entCoord_zero_cons p g b ω'

/--
[esd_entCoord0_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_entCoord0_expect_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin (n+1) → Bool) → ℝ} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g 0) = OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => p * esd_Phi (g (Fin.cons true ω')) + (1-p) * esd_Phi (g (Fin.cons false ω')) - esd_Phi (p * g (Fin.cons true ω') + (1-p) * g (Fin.cons false ω'))) := by
-- proof
  apply StatMech.Probability.esd_entCoord0_expect p g

/--
[esd_entCoordSucc_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_entCoordSucc_expect_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin (n+1) → Bool) → ℝ}
  {e' : Fin n} :
-- imply
  OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g (Fin.succ e')) = (1-p) * OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p (fun ω' => g (Fin.cons false ω')) e') + p * OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p (fun ω' => g (Fin.cons true ω')) e') := by
-- proof
  apply StatMech.Probability.esd_entCoordSucc_expect p g e'

/--
[esd_ent_cons_split](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_ent_cons_split_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin (n+1) → Bool) → ℝ} :
-- imply
  esd_ent (OSSS.bernoulliWeight p) g = ((1-p) * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => esd_Phi (g (Fin.cons false ω'))) - esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω')))) + p * (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' : Fin n → Bool => esd_Phi (g (Fin.cons true ω'))) - esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω'))))) + (p * esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω'))) + (1-p) * esd_Phi (OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω'))) - esd_Phi ((1-p) * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons false ω')) + p * OSSS.expect (OSSS.bernoulliWeight p) (fun ω' => g (Fin.cons true ω')))) := by
-- proof
  apply StatMech.Probability.esd_ent_cons_split p g

/--
[esd_ent_fin_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_ent_fin_zero_eq
  [Fintype E]
  [DecidableEq E]
  {p : ℝ}
  {g : (Fin 0 → Bool) → ℝ} :
-- imply
  esd_ent (OSSS.bernoulliWeight p) g = 0 := by
-- proof
  apply StatMech.Probability.esd_ent_fin_zero p g

/--
[esd_subadditivity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Probability/EntropySubadd.lean)
-/
@[path]
private lemma esd_subadditivity_eq
  [Fintype E]
  [DecidableEq E]
  {n : ℕ}
  {p : ℝ}
  {g : (Fin n → Bool) → ℝ}
-- given
  (hp0 : 0 < p)
  (hp1 : p < 1)
  (hg : ∀ ω, 0 ≤ g ω) :
-- imply
  esd_ent (OSSS.bernoulliWeight p) g ≤ ∑ e : Fin n, OSSS.expect (OSSS.bernoulliWeight p) (esd_entCoord p g e) := by
-- proof
  apply StatMech.Probability.esd_subadditivity hp0 hp1 g hg


-- created on 2026-10-23
