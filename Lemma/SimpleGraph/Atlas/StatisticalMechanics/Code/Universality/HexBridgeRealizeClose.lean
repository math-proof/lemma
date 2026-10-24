import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Universality.HexBridgeRealizeClose
open StatMech StatMech.Universality


/--
[hbr_fiberSum_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_fiberSum_nonneg_eq
  {W I : Type}
  {E : HexColumnEmb W I}
  {v : ℕ} :
-- imply
  0 ≤ E.fiberSum v := by
-- proof
  apply StatMech.Universality.hbr_fiberSum_nonneg E v

/--
[hbr_fiberSum_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_fiberSum_pos_eq
  {W I : Type}
  {E : HexColumnEmb W I}
  {v : ℕ}
  {i0 : I}
-- given
  (hsc : E.scale i0 = v)
  (hpos : 0 < E.wtSAW (E.emb i0))
  (hsum : Summable (fun i : {i // E.scale i = v} => E.wtSAW (E.emb i.1))) :
-- imply
  0 < E.fiberSum v := by
-- proof
  apply StatMech.Universality.hbr_fiberSum_pos E v i0 hsc hpos hsum

/--
[hbr_cutB_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_cutB_of_bijection_eq
  {W Iυ : Type}
  {Eυ : HexColumnEmb W Iυ}
  {K : ℝ}
  {Cut : HexHighestCut K}
  {v : ℕ}
-- given
  (e : Cut.B ≃ {i : Iυ // Eυ.scale i = v + 1})
  (hw : ∀ b, Cut.wtB b = Eυ.wtSAW (Eυ.emb (e b).1)) :
-- imply
  (∑' b, Cut.wtB b) = Eυ.fiberSum (v + 1) := by
-- proof
  apply StatMech.Universality.hbr_cutB_of_bijection Eυ Cut v e hw

/--
[hbr_lamCum_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_lamCum_telescope_eq
  {f : ℕ → ℝ}
  {v : ℕ} :
-- imply
  hbr_lamCum f (v + 1) - hbr_lamCum f v = f (v + 1) := by
-- proof
  apply StatMech.Universality.hbr_lamCum_telescope f v

/--
[hbr_lamCum_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_lamCum_mono_eq
  {f : ℕ → ℝ}
  {v : ℕ}
-- given
  (hf : ∀ n, 0 ≤ f n) :
-- imply
  hbr_lamCum f v ≤ hbr_lamCum f (v + 1) := by
-- proof
  apply StatMech.Universality.hbr_lamCum_mono f hf v

/--
[hbr_cutD_of_bijection](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_cutD_of_bijection_eq
  {W Ila : Type}
  {Ela : HexColumnEmb W Ila}
  {K : ℝ}
  {Cut : HexHighestCut K}
  {lam : ℕ → ℝ}
  {v : ℕ}
-- given
  (htel : lam (v + 1) - lam v = Ela.fiberSum (v + 1))
  (e : Cut.D ≃ {i : Ila // Ela.scale i = v + 1})
  (hw : ∀ d, Cut.wtγ d = Ela.wtSAW (Ela.emb (e d).1)) :
-- imply
  (∑' d, Cut.wtγ d) = lam (v + 1) - lam v := by
-- proof
  apply StatMech.Universality.hbr_cutD_of_bijection Ela Cut lam v htel e hw

/--
[hbr_hexZ_chi_div_of_bijections](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_hexZ_chi_div_of_bijections_eq
  {c : ℕ → ℝ}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
  {Ila : Type}
  {Ela : HexColumnEmb ℕ Ila}
  {tau : ℕ → ℝ}
  {Cut : ℕ → HexHighestCut hexChiE⁻¹}
-- given
  (hτnn : ∀ v, 0 ≤ tau v)
  (eB : ∀ v, (Cut v).B ≃ {i : Iυ // Eυ.scale i = v + 1})
  (hwB : ∀ v, ∀ b, (Cut v).wtB b = Eυ.wtSAW (Eυ.emb (eB v b).1))
  (eD : ∀ v, (Cut v).D ≃ {i : Ila // Ela.scale i = v + 1})
  (hwD : ∀ v, ∀ d, (Cut v).wtγ d = Ela.wtSAW (Ela.emb (eD v d).1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hbr_lamCum (Ela.fiberSum) v + hexCt * tau v + Eυ.fiberSum v = 1)
  (hυpos : ∀ v, 1 ≤ v → 0 < Eυ.fiberSum v)
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hbr_hexZ_chi_div_of_bijections c Eτ Eυ Ela tau hτnn Cut eB hwB eD hwD hbdry hυpos hEτ hτdiv hEυ

/--
[hbr_witnessEmb_fiberSum_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_witnessEmb_fiberSum_one_eq :
-- imply
  hbr_witnessEmb.fiberSum 1 = 1 := by
-- proof
  apply StatMech.Universality.hbr_witnessEmb_fiberSum_one

/--
[hbr_bijection_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexBridgeRealizeClose.lean)
-/
@[path]
private lemma hbr_bijection_fires_eq
  {K : ℝ}
  {Cut : HexHighestCut K}
-- given
  (e : Cut.B ≃ {i : Unit // hbr_witnessEmb.scale i = 0 + 1})
  (hw : ∀ b, Cut.wtB b = hbr_witnessEmb.wtSAW (hbr_witnessEmb.emb (e b).1)) :
-- imply
  (∑' b, Cut.wtB b) = 1 := by
-- proof
  apply StatMech.Universality.hbr_bijection_fires Cut e hw


-- created on 2026-10-23
