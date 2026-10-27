import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCorrections.Part3
open StatMech StatMech.FrontierA


/--
[grahamPairSupport_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamPairSupport_chain_eq
  [Fintype V]
  [DecidableEq V]
  {i m k : V} :
-- imply
  grahamPairSupport i m ∆ grahamPairSupport m k = grahamPairSupport i k := by
-- proof
  apply StatMech.FrontierA.grahamPairSupport_chain i m k

/--
[spinProd_grahamPairSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma spinProd_grahamPairSupport_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {x y : V} :
-- imply
  spinProd (grahamPairSupport x y) s = spin s x * spin s y := by
-- proof
  apply StatMech.FrontierA.spinProd_grahamPairSupport s x y

/--
[spinProd_grahamFourSupport](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma spinProd_grahamFourSupport_eq
  [Fintype V]
  [DecidableEq V]
  {s : ConfigSpace V}
  {i j k l : V} :
-- imply
  spinProd (grahamFourSupport i j k l) s = (spin s i * spin s j) * (spin s k * spin s l) := by
-- proof
  apply StatMech.FrontierA.spinProd_grahamFourSupport s i j k l

/--
[grahamTwoPoint_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamTwoPoint_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V} :
-- imply
  grahamTwoPoint E J x y = expJ E J (fun _ => 0) (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.FrontierA.grahamTwoPoint_eq_expJ E J x y

/--
[grahamFourPoint_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamFourPoint_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l : V} :
-- imply
  grahamFourPoint E J i j k l = expJ E J (fun _ => 0) (fun s => (spin s i * spin s j) * (spin s k * spin s l)) := by
-- proof
  apply StatMech.FrontierA.grahamFourPoint_eq_expJ E J i j k l

/--
[grahamUrsell4_eq_expJ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamUrsell4_eq_expJ_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l : V} :
-- imply
  grahamUrsell4 E J i j k l = expJ E J (fun _ => 0) (fun s => (spin s i * spin s j) * (spin s k * spin s l)) - expJ E J (fun _ => 0) (fun s => spin s i * spin s j) * expJ E J (fun _ => 0) (fun s => spin s k * spin s l) - expJ E J (fun _ => 0) (fun s => spin s i * spin s k) * expJ E J (fun _ => 0) (fun s => spin s j * spin s l) - expJ E J (fun _ => 0) (fun s => spin s i * spin s l) * expJ E J (fun _ => 0) (fun s => spin s j * spin s k) := by
-- proof
  apply StatMech.FrontierA.grahamUrsell4_eq_expJ E J i j k l

/--
[grahamTwoPoint_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamTwoPoint_self_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x : V} :
-- imply
  grahamTwoPoint E J x x = 1 := by
-- proof
  apply StatMech.FrontierA.grahamTwoPoint_self E J x

/--
[grahamTwoPoint_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamTwoPoint_comm_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V} :
-- imply
  grahamTwoPoint E J x y = grahamTwoPoint E J y x := by
-- proof
  apply StatMech.FrontierA.grahamTwoPoint_comm E J x y

/--
[grahamBridgeGap_comm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamBridgeGap_comm_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i k m : V} :
-- imply
  grahamBridgeGap E J i k m = grahamBridgeGap E J k i m := by
-- proof
  apply StatMech.FrontierA.grahamBridgeGap_comm E J i k m

/--
[grahamCorrectedRHS_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamCorrectedRHS_eq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V} :
-- imply
  grahamCorrectedRHS E J i j k l m = -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m * grahamTwoPoint E J k m * grahamTwoPoint E J l m) + -2 * (grahamBridgeGap E J i k m * grahamBridgeGap E J j k m * grahamTwoPoint E J k l) + -2 * (grahamTwoPoint E J i m * grahamTwoPoint E J j m * grahamBridgeGap E J i k m * grahamBridgeGap E J i l m) := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedRHS_eq E J i j k l m

/--
[grahamTwoPoint_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamTwoPoint_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {x y : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  0 ≤ grahamTwoPoint E J x y := by
-- proof
  apply StatMech.FrontierA.grahamTwoPoint_nonneg E J hJ x y

/--
[grahamBridgeGap_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamBridgeGap_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i k m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  0 ≤ grahamBridgeGap E J i k m := by
-- proof
  apply StatMech.FrontierA.grahamBridgeGap_nonneg E J hJ i k m

/--
[grahamLeadingTerm_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamLeadingTerm_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  grahamLeadingTerm E J i j k l m ≤ 0 := by
-- proof
  apply StatMech.FrontierA.grahamLeadingTerm_nonpos E J hJ i j k l m

/--
[grahamKCorrection_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamKCorrection_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  grahamKCorrection E J i j k l m ≤ 0 := by
-- proof
  apply StatMech.FrontierA.grahamKCorrection_nonpos E J hJ i j k l m

/--
[grahamICorrection_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamICorrection_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  grahamICorrection E J i j k l m ≤ 0 := by
-- proof
  apply StatMech.FrontierA.grahamICorrection_nonpos E J hJ i j k l m

/--
[grahamCorrectedRHS_le_leading](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamCorrectedRHS_le_leading_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  grahamCorrectedRHS E J i j k l m ≤ grahamLeadingTerm E J i j k l m := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedRHS_le_leading E J hJ i j k l m

/--
[grahamCorrectedRHS_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamCorrectedRHS_nonpos_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l m : V}
-- given
  (hJ : ∀ e ∈ E, 0 ≤ J e) :
-- imply
  grahamCorrectedRHS E J i j k l m ≤ 0 := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedRHS_nonpos E J hJ i j k l m

/--
[grahamCorrectedRHS_aux_eq_l](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCorrections.lean)
-/
@[path]
private lemma grahamCorrectedRHS_aux_eq_l_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {J : Sym2 V → ℝ}
  {i j k l : V} :
-- imply
  grahamCorrectedRHS E J i j k l l = -2 * (grahamTwoPoint E J i l * grahamTwoPoint E J j l * grahamTwoPoint E J k l) + -2 * (grahamBridgeGap E J i k l * grahamBridgeGap E J j k l * grahamTwoPoint E J k l) := by
-- proof
  apply StatMech.FrontierA.grahamCorrectedRHS_aux_eq_l E J i j k l


-- created on 2026-10-23
