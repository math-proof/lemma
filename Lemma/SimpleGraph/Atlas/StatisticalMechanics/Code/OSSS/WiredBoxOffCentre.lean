import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.OSSS.WiredBoxOffCentre.Part4
open StatMech StatMech.OSSS StatMech.OSSS.WiredBoxOffCentre


/--
[centeredRadius_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredRadius_zero_eq
  {d : Nat}
  {y : Site d} :
-- imply
  centeredRadius 0 y = siteRadius y := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredRadius_zero y

/--
[zeroWithinToBoxHom_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma zeroWithinToBoxHom_val_eq
  {d m R : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
  {y : centeredClosedBox (0 : Site d) m}
-- given
  (hmR : m <= R) :
-- imply
  ((zeroWithinToBoxHom d m R hmR omega y : boxVerts d R) : Site d) = y := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.zeroWithinToBoxHom_val d m R hmR omega y

/--
[zeroWithinToBoxHom_origin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma zeroWithinToBoxHom_origin_eq
  {d m R : Nat}
  {omega : ConfigSpace (Sym2 (Site d))}
-- given
  (hmR : m <= R) :
-- imply
  zeroWithinToBoxHom d m R hmR omega ⟨(0 : Site d), center_mem_centeredClosedBox 0 m⟩ = IsingFK.boxOrigin d R := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.zeroWithinToBoxHom_origin d m R hmR omega

/--
[transShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma transShellEvent_increasing_eq
  {d k : Nat}
  {x : Site d} :
-- imply
  IsIncreasing (transShellEvent d k x) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.transShellEvent_increasing d k x

/--
[centeredShellEvent_increasing](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredShellEvent_increasing_eq
  {d k : Nat} :
-- imply
  IsIncreasing (centeredShellEvent d k) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredShellEvent_increasing d k

/--
[centeredShellEvent_eq_connToBdryEventLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredShellEvent_eq_connToBdryEventLE_eq
  {d k : Nat}
-- given
  (hk1 : 1 <= k) :
-- imply
  centeredShellEvent d k = connToBdryEventLE d (n_le_two_mul k) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredShellEvent_eq_connToBdryEventLE d k hk1

/--
[openSub_boxRestrict_liftActive_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma openSub_boxRestrict_liftActive_eq_eq
  {d R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))} :
-- imply
  openSub (boxGraph d R) (boxRestrict d R (liftCfg (WiredBoxDifferential.boxActiveEdge d R) (restrictActive (boxGraph d R) rho))) = openSub (boxGraph d R) rho := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.openSub_boxRestrict_liftActive_eq d R rho

/--
[activeCrossInd_eq_connToBdry_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma activeCrossInd_eq_connToBdry_indicator_eq
  {d R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hR : 1 <= R) :
-- imply
  AdaptiveCovLowerGeom.crossIndG (WiredBoxDifferential.boxActiveEdge d R) 0 R (restrictActive (boxGraph d R) rho) = ({eta : ConfigSpace (Sym2 (boxVerts d R)) | ConnToBdry (boxGraph d R) (boxBoundary d R) eta (IsingFK.boxOrigin d R)}).indicator (fun _ => (1 : Real)) rho := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.activeCrossInd_eq_connToBdry_indicator d R hR rho

/--
[restrictActive_boxRestrictLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma restrictActive_boxRestrictLE_eq
  {d : Nat}
  {r R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hrR : r <= R) :
-- imply
  restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR) (restrictActive (boxGraph d R) rho) = restrictActive (boxGraph d r) (boxRestrictLE d hrR rho) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.restrictActive_boxRestrictLE d hrR rho

/--
[innerCrossInd_restrictActive_eq_centeredShell_indicator](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma innerCrossInd_restrictActive_eq_centeredShell_indicator_eq
  {d k : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d (2 * k)))}
-- given
  (hk1 : 1 <= k) :
-- imply
  WiredBoxLocalized.innerCrossInd d k (restrictActive (boxGraph d (2 * k)) rho) = (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.innerCrossInd_restrictActive_eq_centeredShell_indicator d k hk1 rho

/--
[wiredOuterInnerTheta_eq_centeredShellMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterInnerTheta_eq_centeredShellMass_eq
  {d k : Nat}
  {q beta : Real}
-- given
  (hk1 : 1 <= k)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  WiredBoxLocalized.wiredOuterInnerTheta d q beta k = ∑ rho, (centeredShellEvent d k).indicator (fun _ => (1 : Real)) rho * wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) (1 - Real.exp (-beta)) q rho := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterInnerTheta_eq_centeredShellMass d k hk1 q beta hq hbeta

/--
[boxActiveEdgeLE_ambient](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma boxActiveEdgeLE_ambient_eq
  {d : Nat}
  {r R : Nat}
  {e : (boxGraph d r).edgeSet}
-- given
  (hrR : r <= R) :
-- imply
  WiredBoxDifferential.boxActiveEdge d R (WiredBoxLocalized.boxActiveEdgeLE d hrR e) = WiredBoxDifferential.boxActiveEdge d r e := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.boxActiveEdgeLE_ambient d hrR e

/--
[openSubgraph_liftInner_le_extendOuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma openSubgraph_liftInner_le_extendOuter_eq
  {d : Nat}
  {r R : Nat}
  {rho : ConfigSpace (Sym2 (boxVerts d R))}
-- given
  (hrR : r <= R) :
-- imply
  openSubgraph d (liftCfg (WiredBoxDifferential.boxActiveEdge d r) (restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR) (restrictActive (boxGraph d R) rho))) <= openSubgraph d (extendEdge d R rho) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.openSubgraph_liftInner_le_extendOuter d hrR rho

/--
[openSubgraph_liftInner_le_liftOuter](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma openSubgraph_liftInner_le_liftOuter_eq
  {d : Nat}
  {r R : Nat}
  {omega : ConfigSpace (boxGraph d R).edgeSet}
-- given
  (hrR : r <= R) :
-- imply
  openSubgraph d (liftCfg (WiredBoxDifferential.boxActiveEdge d r) (restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d hrR) omega)) <= openSubgraph d (liftCfg (WiredBoxDifferential.boxActiveEdge d R) omega) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.openSubgraph_liftInner_le_liftOuter d hrR omega

/--
[innerCrossInd_le_fullOuterCrossInd](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma innerCrossInd_le_fullOuterCrossInd_eq
  {d n : Nat}
  {omega : ConfigSpace (boxGraph d (2 * n)).edgeSet} :
-- imply
  WiredBoxLocalized.innerCrossInd d n omega <= AdaptiveCovLowerGeom.crossIndG (WiredBoxDifferential.boxActiveEdge d (2 * n)) 0 n omega := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.innerCrossInd_le_fullOuterCrossInd d n omega

/--
[centeredWithinToTransHom_val](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredWithinToTransHom_val_eq
  {d n k : Nat}
  {x : Site d}
  {rho : ConfigSpace (Sym2 (boxVerts d (2 * n)))}
  {y : centeredClosedBox x k}
-- given
  (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n)) :
-- imply
  ((centeredWithinToTransHom d n k x hsub rho y : fvs_transBoxVerts d (2 * k) x) : Site d) = y := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredWithinToTransHom_val d n k x hsub rho y

/--
[centeredWithinToTransHom_center](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredWithinToTransHom_center_eq
  {d n k : Nat}
  {x : Site d}
  {rho : ConfigSpace (Sym2 (boxVerts d (2 * n)))}
-- given
  (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n)) :
-- imply
  centeredWithinToTransHom d n k x hsub rho ⟨x, center_mem_centeredClosedBox x k⟩ = transBoxCenter d (2 * k) x := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredWithinToTransHom_center d n k x hsub rho

/--
[outerInnerConn_subset_transShell](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma outerInnerConn_subset_transShell_eq
  {d n k : Nat}
  {x : Site d}
  {rho : ConfigSpace (Sym2 (boxVerts d (2 * n)))}
-- given
  (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
  (hconn : ConnectedToSet d (liftCfg (WiredBoxDifferential.boxActiveEdge d n) (restrictConfig (WiredBoxLocalized.boxActiveEdgeLE d (WiredBoxLocalized.n_le_two_mul n)) (restrictActive (boxGraph d (2 * n)) rho))) x (centeredBoundary x k)) :
-- imply
  ocd_innerRestrict (flc_incl hsub) rho ∈ transShellEvent d k x := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.outerInnerConn_subset_transShell d n k x hsub rho hconn

/--
[wiredOuterInnerConn_le_theta_strict_of_domain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterInnerConn_le_theta_strict_of_domain_eq
  {d n k : Nat}
  {x : Site d}
  {q beta : Real}
-- given
  (hx : x ∈ box d n)
  (hk1 : 1 <= k)
  (hkn : 2 * k < n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hsub : fvs_transBox d (2 * k) x ⊆ box d (2 * n))
  (hdom : (∑ rho, (ocd_innerRestrict (flc_incl hsub) ⁻¹' transShellEvent d k x).indicator (fun _ => (1 : Real)) rho * wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) (1 - Real.exp (-beta)) q rho) <= WiredBoxLocalized.wiredOuterInnerTheta d q beta k) :
-- imply
  WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <= WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterInnerConn_le_theta_strict_of_domain d n k x hx hk1 hkn q beta hq hbeta hsub hdom

/--
[centeredRadius_transEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma centeredRadius_transEquiv_eq
  {d R : Nat}
  {x : Site d}
  {y : boxVerts d R} :
-- imply
  centeredRadius x (fvs_transEquiv d R x y : Site d) = siteRadius (y : Site d) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.centeredRadius_transEquiv d R x y

/--
[transEquiv_boxOrigin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma transEquiv_boxOrigin_eq
  {d R : Nat}
  {x : Site d} :
-- imply
  fvs_transEquiv d R x (IsingFK.boxOrigin d R) = transBoxCenter d R x := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.transEquiv_boxOrigin d R x

/--
[reCfgIso_preimage_centeredShellEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma reCfgIso_preimage_centeredShellEvent_eq
  {d k : Nat}
  {x : Site d} :
-- imply
  reCfgIso (fvs_transEquiv d (2 * k) x) ⁻¹' centeredShellEvent d k = transShellEvent d k x := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.reCfgIso_preimage_centeredShellEvent d k x

/--
[transShellEvent_mass_eq_centered](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma transShellEvent_mass_eq_centered_eq
  {d k : Nat}
  {x : Site d}
  {p q : Real} :
-- imply
  (∑ rho, (transShellEvent d k x).indicator (fun _ => (1 : Real)) rho * wiredFkProb (fvs_transBoxGraph d (2 * k) x) (fvs_transBoxBoundary d (2 * k) x) p q rho) = ∑ eta, (centeredShellEvent d k).indicator (fun _ => (1 : Real)) eta * wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q eta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.transShellEvent_mass_eq_centered d k x p q

/--
[transShellEvent_domain_dominated](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma transShellEvent_domain_dominated_eq
  {d n k : Nat}
  {x : Site d}
  {p q : Real}
-- given
  (hx : x ∈ box d n)
  (hk1 : 1 <= k)
  (hkn : 2 * k < n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 <= q) :
-- imply
  (∑ rho, (ocd_innerRestrict (flc_incl (show fvs_transBox d (2 * k) x ⊆ box d (2 * n) by intro y hy i have hyi : ((y - x) i).natAbs <= 2 * k := hy i have hxi : (x i).natAbs <= n := hx i have hEq : y i = (y i - x i) + x i := by ring calc (y i).natAbs = ((y i - x i) + x i).natAbs := by rw [← hEq] _ <= (y i - x i).natAbs + (x i).natAbs := Int.natAbs_add_le _ _ _ = ((y - x) i).natAbs + (x i).natAbs := by simp [Pi.sub_apply] _ <= 2 * k + n := Nat.add_le_add hyi hxi _ <= 2 * n := by omega)) ⁻¹' transShellEvent d k x).indicator (fun _ => (1 : Real)) rho * wiredFkProb (boxGraph d (2 * n)) (boxBoundary d (2 * n)) p q rho) <= ∑ eta, (centeredShellEvent d k).indicator (fun _ => (1 : Real)) eta * wiredFkProb (boxGraph d (2 * k)) (boxBoundary d (2 * k)) p q eta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.transShellEvent_domain_dominated d n k x hx hk1 hkn hp hp1 hq

/--
[wiredOuterInnerConn_le_theta_strict](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterInnerConn_le_theta_strict_eq
  {d n k : Nat}
  {x : Site d}
  {q beta : Real}
-- given
  (hx : x ∈ box d n)
  (hk1 : 1 <= k)
  (hkn : 2 * k < n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <= WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterInnerConn_le_theta_strict d n k x hx hk1 hkn q beta hq hbeta

/--
[wiredOuterInner_strictTranslationComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterInner_strictTranslationComparison_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  forall x, x ∈ WiredBoxDifferential.osssBoxFinset d n -> forall k, k ∈ Finset.Icc 1 (n / 2) -> 2 * k < n -> WiredBoxLocalized.wiredOuterInnerConn d n q beta x k <= WiredBoxLocalized.wiredOuterInnerTheta d q beta k := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterInner_strictTranslationComparison d n q beta hq hbeta

/--
[wiredOuterInnerDenom_le_eight_sig](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterInnerDenom_le_eight_sig_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  WiredBoxLocalized.wiredOuterInnerDenom d n q beta <= 8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterInnerDenom_le_eight_sig d n q beta hq hbeta

/--
[wired_outer_inner_hcov_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_hcov_sharp_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) * (1 - Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n)) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)) <= ∑ e, Lindeberg.cov (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) (Lindeberg.coord e) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_hcov_sharp d n hn q beta hq hbeta

/--
[wired_outer_inner_differential_sharp](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_differential_sharp_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  exists cR : Real, 0 < cR ∧ cR * (Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) * (1 - Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n)) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) b) q (WiredBoxLocalized.innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_differential_sharp d n hd hn q beta hq hbeta

/--
[wired_outer_inner_differential_sharp_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_differential_sharp_uniform_eq
  {d n : Nat}
  {q beta : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta) :
-- imply
  Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) * (1 - Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n)) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real)) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) b) q (WiredBoxLocalized.innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_differential_sharp_uniform d n hn q beta hq hbeta

/--
[wired_outer_inner_one_sub_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_one_sub_lower_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (ActiveEdgeDifferential.incidentEdges (WiredBoxDifferential.boxActiveEndU d (2 * n)) (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod (fun _ => Real.exp (-beta0)) <= 1 - Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_one_sub_lower d n hn q beta beta0 hq hbeta hbeta0

/--
[wiredOuterIncident_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterIncident_card_le_eq
  {d R : Nat} :
-- imply
  (ActiveEdgeDifferential.incidentEdges (WiredBoxDifferential.boxActiveEndU d R) (WiredBoxDifferential.boxActiveEndV d R) 0).card <= 2 * d := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterIncident_card_le d R

/--
[wiredOuterIncident_prod_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wiredOuterIncident_prod_lower_eq
  {d R : Nat}
  {beta0 : Real}
-- given
  (hbeta0 : 0 <= beta0) :
-- imply
  Real.exp (-beta0) ^ (2 * d) <= (ActiveEdgeDifferential.incidentEdges (WiredBoxDifferential.boxActiveEndU d R) (WiredBoxDifferential.boxActiveEndV d R) 0).prod (fun _ => Real.exp (-beta0)) := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wiredOuterIncident_prod_lower d R beta0 hbeta0

/--
[wired_outer_inner_differential_inequality](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_differential_inequality_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hd : 1 <= d)
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  exists c : Real, 0 < c ∧ c * (Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) b) q (WiredBoxLocalized.innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_differential_inequality d n hd hn q beta beta0 hq hbeta hbeta0

/--
[wired_outer_inner_differential_uniform](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_differential_uniform_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  (ActiveEdgeDifferential.incidentEdges (WiredBoxDifferential.boxActiveEndU d (2 * n)) (WiredBoxDifferential.boxActiveEndV d (2 * n)) 0).prod (fun _ => Real.exp (-beta0)) * (Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) b) q (WiredBoxLocalized.innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_differential_uniform d n hn q beta beta0 hq hbeta hbeta0

/--
[wired_outer_inner_differential_uniform_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/OSSS/WiredBoxOffCentre.lean)
-/
@[path]
private lemma wired_outer_inner_differential_uniform_box_eq
  {d n : Nat}
  {q beta beta0 : Real}
-- given
  (hn : 1 <= n)
  (hq : 1 <= q)
  (hbeta : 0 < beta)
  (hbeta0 : beta <= beta0) :
-- imply
  Real.exp (-beta0) ^ (2 * d) * (Lindeberg.mean (activeBCProb (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) beta) q) (WiredBoxLocalized.innerCrossInd d n) / (8 * WiredBoxLocalized.wiredOuterInnerSig d n q beta / (n : Real))) <= deriv (fun b => activeBCMean (boxGraph d (2 * n)) (WiredBoxDifferential.wiredBoxBoundaryGraph d (2 * n)) (betaParams (fun _ => 1) b) q (WiredBoxLocalized.innerCrossInd d n)) beta := by
-- proof
  apply StatMech.OSSS.WiredBoxOffCentre.wired_outer_inner_differential_uniform_box d n hn q beta beta0 hq hbeta hbeta0


-- created on 2026-10-23
