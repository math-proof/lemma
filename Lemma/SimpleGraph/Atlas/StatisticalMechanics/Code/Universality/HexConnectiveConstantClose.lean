import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexConnectiveConstantClose.Part5
open StatMech StatMech.Universality


/--
[hxf_bdry_combined](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_bdry_combined_eq
  {Iυ Ila : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {Ela : HexColumnEmb ℕ Ila}
  {tau : ℕ → ℝ}
  {B : ℕ → HexFObsBoundaryData}
-- given
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
  (hτEq : ∀ v, (B v).tau = tau v)
  (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v) :
-- imply
  ∀ v, 1 ≤ v → hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1 := by
-- proof
  apply StatMech.Universality.hxf_bdry_combined Eυ Ela tau B hFa hlamEq hτEq hυEq

/--
[hxf_hexZ_chi_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_hexZ_chi_div_eq
  {c : ℕ → ℝ}
  {Iυ Ila : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {Ela : HexColumnEmb ℕ Ila}
  {tau : ℕ → ℝ}
  {B : ℕ → HexFObsBoundaryData}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {S : HexSideContour Iτ tau}
-- given
  (hτnn : ∀ v, 0 ≤ tau v)
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
  (hτEq : ∀ v, (B v).tau = tau v)
  (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
  (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
  (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
  (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
  (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
  (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
  (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hxf_hexZ_chi_div c Eυ Ela tau hτnn B hFa hlamEq hτEq hυEq Cut eB hwB eD hwD hυpos S hEτ hEυ

/--
[hxf_hex_connective_constant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_hex_connective_constant_eq
  {c : ℕ → ℝ}
  {Iυ Ila : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {Ela : HexColumnEmb ℕ Ila}
  {tau : ℕ → ℝ}
  {B : ℕ → HexFObsBoundaryData}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
  {Iτ : Type}
  {S : HexSideContour Iτ tau}
-- given
  (hge : ∀ n, 1 ≤ c n)
  (hsub : Submultiplicative c)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hFa : ∀ v, 1 ≤ v → (B v).Fa = 1)
  (hlamEq : ∀ v, (B v).lam = hbr_lamCum (Ela.fiberSum) v)
  (hτEq : ∀ v, (B v).tau = tau v)
  (hυEq : ∀ v, (B v).ups = Eυ.fiberSum v)
  (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
  (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
  (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
  (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
  (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
  (hEτ : S.Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (Col : ∀ T, HexColumn T hexChiE)
  (HW : ∀ x, 0 < x → x < hexChiE → ∀ N, HexHWDataRecon c (fun T => (Col T).colSum x) x N) :
-- imply
  ∃ kappa : ℝ, 0 < kappa ∧ Tendsto (fun n => (c n) ^ ((n : ℝ)⁻¹)) atTop (𝓝 kappa) ∧ kappa = Real.sqrt (2 + Real.sqrt 2) := by
-- proof
  apply StatMech.Universality.hxf_hex_connective_constant c hge hsub Eυ Ela tau hτnn B hFa hlamEq hτEq hυEq Cut eB hwB eD hwD hυpos S hEτ hEυ Col HW

/--
[hxf_hexChiE_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_hexChiE_lt_one_eq :
-- imply
  hexChiE < 1 := by
-- proof
  apply StatMech.Universality.hxf_hexChiE_lt_one

/--
[hxf_one_le_chiInv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_one_le_chiInv_eq :
-- imply
  1 ≤ hexChiE⁻¹ := by
-- proof
  apply StatMech.Universality.hxf_one_le_chiInv

/--
[hxf_wc_wt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_wc_wt_eq
  {n : ℕ} :
-- imply
  hxf_wc n * hexChiE ^ n = 1 := by
-- proof
  apply StatMech.Universality.hxf_wc_wt n

/--
[hxf_wc_wt_nn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_wc_wt_nn_eq
  {n : ℕ} :
-- imply
  0 ≤ hxf_wc n * hexChiE ^ n := by
-- proof
  apply StatMech.Universality.hxf_wc_wt_nn n

/--
[hxf_wE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_wE_eq
  {v : ℕ} :
-- imply
  hxf_wEυ.fiberSum v = 1 := by
-- proof
  apply StatMech.Universality.hxf_wE v

/--
[hxf_wEla_lamCum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_wEla_lamCum_eq
  {v : ℕ} :
-- imply
  hbr_lamCum (hxf_wEla.fiberSum) v = 0 := by
-- proof
  apply StatMech.Universality.hxf_wEla_lamCum v

/--
[hxf_divergence_witness](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_divergence_witness_eq :
-- imply
  ¬ Summable (fun n => hxf_wc n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hxf_divergence_witness

/--
[hxf_divergence_witness_consistent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_divergence_witness_consistent_eq :
-- imply
  ¬ Summable (fun _ : ℕ => (1:ℝ)) := by
-- proof
  apply StatMech.Universality.hxf_divergence_witness_consistent

/--
[hxf_wc_saw_facts](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexConnectiveConstantClose.lean)
-/
@[path]
private lemma hxf_wc_saw_facts_eq :
-- imply
  (∀ n, 1 ≤ hxf_wc n) ∧ Submultiplicative hxf_wc := by
-- proof
  apply StatMech.Universality.hxf_wc_saw_facts


-- created on 2026-10-23
