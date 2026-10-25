import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexBridge.Part6
open StatMech StatMech.Universality StatMech.Universality.HexColumn StatMech.Universality.HexContourEmb StatMech.Universality.HexColumnEmb StatMech.Universality.HexHighestCut StatMech.Universality.HexHWData


/--
[hexBr_pow_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma hexBr_pow_decay_eq
  {x χ : ℝ}
  {T n : ℕ}
-- given
  (hx : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ)
  (hn : T ≤ n) :
-- imply
  x ^ n ≤ (x / χ) ^ T * χ ^ n := by
-- proof
  apply StatMech.Universality.hexBr_pow_decay x χ T n hx hχ hxχ hn

/--
[colSum_crit_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma colSum_crit_summable_eq
  {T : ℕ}
  {χ : ℝ}
  {C : HexColumn T χ} :
-- imply
  Summable (fun w => χ ^ C.len w) := by
-- proof
  apply StatMech.Universality.HexColumn.colSum_crit_summable C

/--
[colSum_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma colSum_summable_eq
  {T : ℕ}
  {χ : ℝ}
  {C : HexColumn T χ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ) :
-- imply
  Summable (fun w => x ^ C.len w) := by
-- proof
  apply StatMech.Universality.HexColumn.colSum_summable C hx hχ hxχ

/--
[colSum_le_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma colSum_le_decay_eq
  {T : ℕ}
  {χ : ℝ}
  {C : HexColumn T χ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ) :
-- imply
  C.colSum x ≤ (x / χ) ^ T * C.colSum χ := by
-- proof
  apply StatMech.Universality.HexColumn.colSum_le_decay C hx hχ hxχ

/--
[colSum_le_pow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma colSum_le_pow_eq
  {T : ℕ}
  {χ : ℝ}
  {C : HexColumn T χ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hχ : 0 < χ)
  (hxχ : x ≤ χ) :
-- imply
  C.colSum x ≤ (x / χ) ^ T := by
-- proof
  apply StatMech.Universality.HexColumn.colSum_le_pow C hx hχ hxχ

/--
[colSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma colSum_nonneg_eq
  {T : ℕ}
  {χ : ℝ}
  {C : HexColumn T χ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x) :
-- imply
  0 ≤ C.colSum x := by
-- proof
  apply StatMech.Universality.HexColumn.colSum_nonneg C hx

/--
[summable_of_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma summable_of_summable_eq
  {E : HexContourEmb W I}
-- given
  (hZ : Summable E.wtSAW) :
-- imply
  Summable E.wtContour := by
-- proof
  apply StatMech.Universality.HexContourEmb.summable_of_summable E hZ

/--
[not_summable_of_not_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma not_summable_of_not_summable_eq
  {E : HexContourEmb W I}
-- given
  (hI : ¬ Summable E.wtContour) :
-- imply
  ¬ Summable E.wtSAW := by
-- proof
  apply StatMech.Universality.HexContourEmb.not_summable_of_not_summable E hI

/--
[tsum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma tsum_le_eq
  {E : HexContourEmb W I}
-- given
  (hZ : Summable E.wtSAW) :
-- imply
  (∑' i, E.wtContour i) ≤ ∑' w, E.wtSAW w := by
-- proof
  apply StatMech.Universality.HexContourEmb.tsum_le E hZ

/--
[fiberSum_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma fiberSum_summable_eq
  {E : HexColumnEmb W I}
-- given
  (hZ : Summable E.wtSAW) :
-- imply
  Summable E.fiberSum := by
-- proof
  apply StatMech.Universality.HexColumnEmb.fiberSum_summable E hZ

/--
[recursion_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma recursion_bound_eq
  {K : ℝ}
  {H : HexHighestCut K}
-- given
  (hK : 0 ≤ K) :
-- imply
  (∑' d, H.wtγ d) ≤ K * (∑' b, H.wtB b) ^ 2 := by
-- proof
  apply StatMech.Universality.HexHighestCut.recursion_bound H hK

/--
[partial_bound](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma partial_bound_eq
  {c υ : ℕ → ℝ}
  {x : ℝ}
  {N : ℕ}
  {H : HexHWData c υ x N} :
-- imply
  ∑ n ∈ Finset.range N, c n * x ^ n ≤ 2 * (∏' T, (1 + υ T)) ^ 2 := by
-- proof
  apply StatMech.Universality.HexHWData.partial_bound H

/--
[hexZ_conv_from_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma hexZ_conv_from_geometry_eq
  {c : ℕ → ℝ}
  {x : ℝ}
-- given
  (hx : 0 ≤ x)
  (hlt : x < hexChiE)
  (hc : ∀ n, 0 ≤ c n)
  (C : ∀ T, HexColumn T hexChiE)
  (H : ∀ N, HexHWData c (fun T => (C T).colSum x) x N) :
-- imply
  Summable (fun n => c n * x ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_conv_from_geometry c x hx hlt hc C H

/--
[hexRec_term_of_cut](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma hexRec_term_of_cut_eq
  {lam ups : ℕ → ℝ}
  {v : ℕ}
  {Cut : HexHighestCut hexChiE}
-- given
  (hD : (∑' d, Cut.wtγ d) = lam (v + 1) - lam v)
  (hB : (∑' b, Cut.wtB b) = ups (v + 1)) :
-- imply
  lam (v + 1) - lam v ≤ hexChiE * (ups (v + 1)) ^ 2 := by
-- proof
  apply StatMech.Universality.hexRec_term_of_cut lam ups v Cut hD hB

/--
[hexZ_chi_div_from_geometry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridge.lean)
-/
@[path]
private lemma hexZ_chi_div_from_geometry_eq
  {c lam tau ups : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (hbdry : ∀ v, 1 ≤ v → hexCl * lam v + hexCt * tau v + ups v = 1)
  (hlamMono : ∀ v, 1 ≤ v → lam v ≤ lam (v + 1))
  (hυpos : ∀ v, 1 ≤ v → 0 < ups v)
  (hυnn : ∀ v, 0 ≤ ups v)
  (hτnn : ∀ v, 0 ≤ tau v)
  (hCutD : ∀ v, 1 ≤ v → (∑' d, (Cut v).wtγ d) = lam (v + 1) - lam v)
  (hCutB : ∀ v, 1 ≤ v → (∑' b, (Cut v).wtB b) = ups (v + 1))
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = ups) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hexZ_chi_div_from_geometry c lam tau ups hbdry hlamMono hυpos hυnn hτnn Cut hCutD hCutB Eτ hEτ hτdiv Eυ hEυ hEυc


-- created on 2026-10-23
