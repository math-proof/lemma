import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.LebowitzPfisterReplicaFiberInequality
open Finset StatMech StatMech.Ising


/--
[mem_lpReplicaDisconnProfileFamily](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma mem_lpReplicaDisconnProfileFamily_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {A : Finset (LPReplicaCurrentVertex V)}
  {S : Finset (Copy (lpReplicaCurrentGraph G sites) m)}
-- given
  (sites : I -> V)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  S ∈ lpReplicaDisconnProfileFamily G sites A m ↔ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) S = A ∧ RandomCurrent.sources (endsM (lpReplicaCurrentGraph G sites) m) (Finset.univ \ S) = ∅ ∧ ¬ RandomCurrent.connK (endsM (lpReplicaCurrentGraph G sites) m) Finset.univ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.mem_lpReplicaDisconnProfileFamily G sites A m S

/--
[lpReplicaDisconnProfileTerm_eq_card_mul_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaDisconnProfileTerm_eq_card_mul_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  lpReplicaDisconnProfileTerm G sites beta J hf r A m = (#(lpReplicaDisconnProfileFamily G sites A m) : Real) * weight (lpReplicaCurrentGraph G sites) beta (lpReplicaCurrentCoupling J hf r) (ofEdgeFun (lpReplicaCurrentGraph G sites) m) := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnProfileTerm_eq_card_mul_weight G sites beta J hf r A m

/--
[lpReplicaCollisionRowGate_of_mem_disconnFamilies](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaCollisionRowGate_of_mem_disconnFamilies_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {Sa : Finset (Copy (lpReplicaCurrentGraph G sites) a)}
  {Sb : Finset (Copy (lpReplicaCurrentGraph G sites) b)}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (a b : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat)
  (hSa : Sa ∈ lpReplicaDisconnProfileFamily G sites A a)
  (hSb : Sb ∈ lpReplicaDisconnProfileFamily G sites B b) :
-- imply
  LPReplicaRowGate G sites (lpReplicaCollisionProfile G sites a b) A (B.map lpReplicaCurrentReflect.toEmbedding) (lpReplicaCollisionRowTag G sites a b Sa Sb) := by
-- proof
  apply StatMech.Ising.lpReplicaCollisionRowGate_of_mem_disconnFamilies G sites a b Sa Sb A B hSa hSb

/--
[lpReplicaDisconnProfileTerm_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaDisconnProfileTerm_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  0 <= lpReplicaDisconnProfileTerm G sites beta J hf r A m := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnProfileTerm_nonneg G sites beta J hf r hbeta hJ hhf hr A m

/--
[lpReplicaRowFiberMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaRowFiberMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (m : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  0 <= lpReplicaRowFiberMass G sites beta J hf r A B m := by
-- proof
  apply StatMech.Ising.lpReplicaRowFiberMass_nonneg G sites beta J hf r hbeta hJ hhf hr A B m

/--
[lpReplicaDisconnProfileTerm_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaDisconnProfileTerm_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  Summable (lpReplicaDisconnProfileTerm G sites beta J hf r A) := by
-- proof
  apply StatMech.Ising.lpReplicaDisconnProfileTerm_summable G sites beta J hf r hbeta hJ hhf hr A

/--
[lpReplicaRowFiberMass_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaRowFiberMass_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  Summable (lpReplicaRowFiberMass G sites beta J hf r A B) := by
-- proof
  apply StatMech.Ising.lpReplicaRowFiberMass_summable G sites beta J hf r hbeta hJ hhf hr A B

/--
[lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr A ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr B ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑' m, lpReplicaRowFiberMass G sites beta J hf r A B m := by
-- proof
  apply StatMech.Ising.lpReplica_sourcePairDisconn_mul_eq_tsum_rowFiberMass G sites beta J hf r hbeta hJ hhf hr A B

/--
[lpReplicaProfileOrbitMass_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (q : (lpReplicaCurrentGraph G sites).edgeFinset -> Nat) :
-- imply
  0 <= lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_nonneg G sites beta J hf r hbeta hJ hhf hr A B q

/--
[lpReplicaProfileOrbitMass_summable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaProfileOrbitMass_summable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  Summable (lpReplicaProfileOrbitMass G sites beta J hf r A B) := by
-- proof
  apply StatMech.Ising.lpReplicaProfileOrbitMass_summable G sites beta J hf r hbeta hJ hhf hr A B

/--
[lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr A ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr B ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 = ∑' q, lpReplicaProfileOrbitMass G sites beta J hf r A B q := by
-- proof
  apply StatMech.Ising.lpReplica_sourcePairDisconn_mul_eq_tsum_profileOrbitMass G sites beta J hf r hbeta hJ hhf hr A B

/--
[lpReplicaAggregateProfileOrbitInequality_of_offdiag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaAggregateProfileOrbitInequality_of_offdiag_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hpoint : ∀ q i j, i ≠ j -> let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 lpReplicaProfileOrbitMass G sites beta J hf r ∅ (Si ∆ Sj ∆ T) q <= lpReplicaProfileOrbitMass G sites beta J hf r Si (Sj ∆ T) q + lpReplicaProfileOrbitMass G sites beta J hf r Sj (Si ∆ T) q) :
-- imply
  LPReplicaAggregateProfileOrbitInequality G sites beta J hf r := by
-- proof
  apply StatMech.Ising.lpReplicaAggregateProfileOrbitInequality_of_offdiag G sites beta J hf r hbeta hJ hhf hr hpoint

/--
[lpReplicaMatchingDisconn_le_of_profileOrbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_profileOrbit_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (horbit : LPReplicaAggregateProfileOrbitInequality G sites beta J hf r) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_profileOrbit G sites beta J hf r hbeta hJ hhf hr horbit

/--
[lpReplica_disconn_fourFunctions_of_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplica_disconn_fourFunctions_of_fiberwise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {A B C D E F : Finset (LPReplicaCurrentVertex V)}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hfiber : ∀ m, lpReplicaRowFiberMass G sites beta J hf r A B m <= lpReplicaRowFiberMass G sites beta J hf r C D m + lpReplicaRowFiberMass G sites beta J hf r E F m) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr A ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr B ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= sourcePairDisconnSum H beta Jr C ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr D ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 + sourcePairDisconnSum H beta Jr E ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr F ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplica_disconn_fourFunctions_of_fiberwise G sites beta J hf r hbeta hJ hhf hr A B C D E F hfiber

/--
[lpReplica_offdiagFourFunctions_of_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplica_offdiagFourFunctions_of_fiberwise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
  {i j : I}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hfiber : LPReplicaOffdiagFiberInequality G sites beta J hf r i j) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r let Si := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) i let Sj := lpMatchingSeamSource (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) j let T := lpMatchingGhostSource (lpReplicaCurrentGhost0 : LPReplicaCurrentVertex V) lpReplicaCurrentGhost1 sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Si ∆ Sj ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= sourcePairDisconnSum H beta Jr Si ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Sj ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 + sourcePairDisconnSum H beta Jr Sj ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * sourcePairDisconnSum H beta Jr (Si ∆ T) ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplica_offdiagFourFunctions_of_fiberwise G sites beta J hf r hbeta hJ hhf hr i j hfiber

/--
[lpReplicaMatchingDisconn_le_of_fiberwise](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/LebowitzPfisterReplicaFiberInequality.lean)
-/
@[path]
private lemma lpReplicaMatchingDisconn_le_of_fiberwise_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  {beta : Real}
  {r : Real}
-- given
  (sites : I -> V)
  (J : Sym2 V -> Real)
  (hf : V -> Real)
  (hbeta : 0 <= beta)
  (hJ : ∀ e, 0 <= J e)
  (hhf : ∀ x, 0 <= hf x)
  (hr : 0 <= r)
  (hfiber : ∀ i j : I, i ≠ j -> LPReplicaOffdiagFiberInequality G sites beta J hf r i j) :
-- imply
  let H := lpReplicaCurrentGraph G sites let Jr := lpReplicaCurrentCoupling J hf r sourcePairDisconnSum H beta Jr ∅ ∅ lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnTwo H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 <= 2 * lpMatchingDisconnZero H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 * lpMatchingDisconnOne H beta Jr (lpReplicaCurrentLeft sites) (lpReplicaCurrentRight sites) lpReplicaCurrentGhost0 lpReplicaCurrentGhost1 := by
-- proof
  apply StatMech.Ising.lpReplicaMatchingDisconn_le_of_fiberwise G sites beta J hf r hbeta hJ hhf hr hfiber


-- created on 2026-10-23
