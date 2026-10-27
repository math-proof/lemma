import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.HexHalfEdgeClose.Part3
open StatMech StatMech.Universality


/--
[hhe_rho_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_rho_norm_eq
-- given
  (h h' : ℤ) :
-- imply
  ‖hhe_rho h h'‖ = 1 := by
-- proof
  apply StatMech.Universality.hhe_rho_norm h h'

/--
[hhe_rho_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_rho_ne_zero_eq
-- given
  (h h' : ℤ) :
-- imply
  hhe_rho h h' ≠ 0 := by
-- proof
  apply StatMech.Universality.hhe_rho_ne_zero h h'

/--
[hhe_hexUnit_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_hexUnit_add_eq
  {k s : ℤ} :
-- imply
  hexUnit (k + s) = hexUnit k * Complex.exp (Complex.I * ((s : ℝ) * (Real.pi / 3))) := by
-- proof
  apply StatMech.Universality.hhe_hexUnit_add k s

/--
[hhe_halfStep_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_halfStep_shift_eq
  {s : ℤ}
-- given
  (h h' : ℤ) :
-- imply
  halfStep (h' + s) = hhe_rho h h' * halfStep (h + s) := by
-- proof
  apply StatMech.Universality.hhe_halfStep_shift h h' s

/--
[hhe_verticesAux_rigid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_verticesAux_rigid_eq
  {ts : List ℤ}
-- given
  (h h' : ℤ) :
-- imply
  ∀ (m m' : ℂ) (s : ℤ), verticesAux m' (h' + s) ts = (verticesAux m (h + s) ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
-- proof
  apply StatMech.Universality.hhe_verticesAux_rigid h h' ts

/--
[hhe_verticesAux_rigid0](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_verticesAux_rigid0_eq
  {ts : List ℤ}
  {m m' : ℂ}
-- given
  (h h' : ℤ) :
-- imply
  verticesAux m' h' ts = (verticesAux m h ts).map (fun z => hhe_rho h h' * (z - m) + m') := by
-- proof
  apply StatMech.Universality.hhe_verticesAux_rigid0 h h' ts m m'

/--
[hhe_nodup_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_nodup_iff_eq
  {ts : List ℤ}
  {m m' : ℂ}
-- given
  (h h' : ℤ) :
-- imply
  (verticesAux m' h' ts).Nodup ↔ (verticesAux m h ts).Nodup := by
-- proof
  apply StatMech.Universality.hhe_nodup_iff h h' ts m m'

/--
[hhe_isSAW_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_isSAW_rebase_eq
  {m m' : ℂ}
  {ts : List ℤ}
-- given
  (h h' : ℤ) :
-- imply
  (ofTurns m' h' ts).IsSAW ↔ (ofTurns m h ts).IsSAW := by
-- proof
  apply StatMech.Universality.hhe_isSAW_rebase m m' h h' ts

/--
[hhe_legalTurns_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_legalTurns_rebase_eq
  {m m' : ℂ}
  {ts : List ℤ}
-- given
  (h h' : ℤ) :
-- imply
  (ofTurns m' h' ts).LegalTurns ↔ (ofTurns m h ts).LegalTurns := by
-- proof
  apply StatMech.Universality.hhe_legalTurns_rebase m m' h h' ts

/--
[hhe_isLegalSAW_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_isLegalSAW_rebase_eq
  {m m' : ℂ}
  {ts : List ℤ}
-- given
  (h h' : ℤ) :
-- imply
  (ofTurns m' h' ts).IsLegalSAW ↔ (ofTurns m h ts).IsLegalSAW := by
-- proof
  apply StatMech.Universality.hhe_isLegalSAW_rebase m m' h h' ts

/--
[hhe_hexSAWwt_rebase](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_hexSAWwt_rebase_eq
  {m m' : ℂ}
  {x : ℝ}
  {ts : List ℤ}
-- given
  (h h' : ℤ) :
-- imply
  hexSAWwt m' h' x ts = hexSAWwt m h x ts := by
-- proof
  apply StatMech.Universality.hhe_hexSAWwt_rebase m m' h h' x ts

/--
[hhe_halfClass_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_halfClass_lower_eq
  {a : ℂ}
  {x : ℝ}
  (htake hdrop)
  {d : {ts // memD ts}}
-- given
  (h0 : ℤ)
  (memD memB : List ℤ → Prop) :
-- imply
  ((hhe_halfClass a h0 x memD memB htake hdrop).lower d).1 = d.1.take (hexW2_cutPos h0 d.1) := by
-- proof
  apply StatMech.Universality.hhe_halfClass_lower a h0 x memD memB d

/--
[hhe_halfClass_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_halfClass_upper_eq
  {a : ℂ}
  {x : ℝ}
  (htake hdrop)
  {d : {ts // memD ts}}
-- given
  (h0 : ℤ)
  (memD memB : List ℤ → Prop) :
-- imply
  ((hhe_halfClass a h0 x memD memB htake hdrop).upper d).1 = d.1.drop (hexW2_cutPos h0 d.1) := by
-- proof
  apply StatMech.Universality.hhe_halfClass_upper a h0 x memD memB d

/--
[hhe_hexZ_chi_div](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_hexZ_chi_div_eq
  {c : ℕ → ℝ}
  {a0 : ℂ}
  {tau : ℕ → ℝ}
  {Iτ : Type}
  {Eτ : HexContourEmb ℕ Iτ}
  {Iυ : Type}
  {Eυ : HexColumnEmb ℕ Iυ}
-- given
  (h0 : ℤ)
  (memA memB : ℕ → List ℤ → Prop)
  (hsub : ∀ v ts, memA v ts → memA (v + 1) ts)
  (HIC : ∀ v, HexHalvesInColumn h0 (fun ts => memA (v + 1) ts ∧ ¬ memA v ts) (memB (v + 1)))
  (hDsum : ∀ v, Summable (fun d : {ts // memA (v + 1) ts ∧ ¬ memA v ts} => hexSAWwt a0 h0 hexChiE d.1))
  (hBsum : ∀ v, Summable (fun b : {ts // memB (v + 1) ts} => hexSAWwt a0 h0 hexChiE b.1))
  (hAsum : ∀ v, Summable (fun n : {ts // memA (v + 1) ts} => hexSAWwt a0 h0 hexChiE n.1))
  (hbdry : ∀ v, 1 ≤ v → hexCl * hpb_lamS a0 h0 hexChiE (memA v) + hexCt * tau v + hpb_upsS a0 h0 hexChiE (memB v) = 1)
  (hlamMono : ∀ v, 1 ≤ v → hpb_lamS a0 h0 hexChiE (memA v) ≤ hpb_lamS a0 h0 hexChiE (memA (v + 1)))
  (hυpos : ∀ v, 1 ≤ v → 0 < hpb_upsS a0 h0 hexChiE (memB v))
  (hτnn : ∀ v, 0 ≤ tau v)
  (hEτ : Eτ.wtSAW = fun n => c n * hexChiE ^ n)
  (hτdiv : (∃ v, 1 ≤ v ∧ 0 < tau v) → ¬ Summable Eτ.wtContour)
  (hEυ : Eυ.wtSAW = fun n => c n * hexChiE ^ n)
  (hEυc : Eυ.fiberSum = fun v => hpb_upsS a0 h0 hexChiE (memB v)) :
-- imply
  ¬ Summable (fun n => c n * hexChiE ^ n) := by
-- proof
  apply StatMech.Universality.hhe_hexZ_chi_div c a0 h0 memA memB tau hsub HIC hDsum hBsum hAsum hbdry hlamMono hυpos hτnn Eτ hEτ hτdiv Eυ hEυ hEυc

/--
[hhe_singleRight_cutPos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_singleRight_cutPos_eq :
-- imply
  hexW2_cutPos 0 [(-1 : ℤ)] = 1 := by
-- proof
  apply StatMech.Universality.hhe_singleRight_cutPos

/--
[hhe_singleRight_upper_fires](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/HexHalfEdgeClose.lean)
-/
@[path]
private lemma hhe_singleRight_upper_fires_eq
  {a : ℂ}
  {x : ℝ} :
-- imply
  hexSAWwt a 0 x ((hhe_halfClass_of_halves a 0 x hexW2_singleRight_memD hhe_singleRight_memB hhe_singleRight_halvesInColumn).upper hexW2_singleRight_elt).1 = hexSAWwt (hexDropMid a 0 [(-1 : ℤ)] (hexW2_cutPos 0 [(-1 : ℤ)])) (0 + ([(-1 : ℤ)].take (hexW2_cutPos 0 [(-1 : ℤ)])).sum) x ([(-1 : ℤ)].drop (hexW2_cutPos 0 [(-1 : ℤ)])) := by
-- proof
  apply StatMech.Universality.hhe_singleRight_upper_fires a x


-- created on 2026-10-23
