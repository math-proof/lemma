import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundaryDerivativeLower
open Finset Filter Topology StatMech StatMech.Ising


/--
[boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : Nat -> V)
  (hinj : Function.Injective (ginibreChainEdge (N := N) v))
  (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
  (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1) :
-- imply
  (∑ j : Fin N, (expJ E (fun a => beta * J a) (fun x => beta * hPlus x) (fun s => bond s (ginibreChainEdge v j)) - expJ E (fun a => beta * J a) (fun x => beta * h x) (fun s => bond s (ginibreChainEdge v j)))) <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_chainDeficit E J hPlus h hJ hdom beta hbeta v N hinj hedge hunit

/--
[boundaryInterfaceFreeEnergy_deriv_ge_chainCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_chainCross_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : Nat -> V)
  (hinj : Function.Injective (ginibreChainEdge (N := N) v))
  (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
  (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1) :
-- imply
  (∑ j : Fin N, (expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v j.val)) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v (j.val + 1))) - expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v (j.val + 1))) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v j.val)))) <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_chainCross E J hPlus h hJ hdom beta hbeta v N hinj hedge hunit

/--
[boundaryInterfaceFreeEnergy_deriv_ge_extendedChainAbsCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_extendedChainAbsCross_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : Nat -> V)
  (hinj : Function.Injective (ginibreChainEdge (N := N) v))
  (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
  (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
  (hend : v 0 ≠ v N)
  (hplusTop : hPlus (v 0) = 1)
  (hmixTop : h (v 0) = -1)
  (hplusBottom : hPlus (v N) = 1)
  (hmixBottom : h (v N) = 1) :
-- imply
  (expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v 0)) + expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v 0))) + (∑ j : Fin N, |expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v j.val)) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v (j.val + 1))) - expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v (j.val + 1))) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v j.val))|) + (expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v N)) - expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v N))) <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_extendedChainAbsCross E J hPlus h hJ hdom beta hbeta v N hinj hedge hunit hend hplusTop hmixTop hplusBottom hmixBottom

/--
[boundaryInterfaceFreeEnergy_deriv_ge_extendedChainFamilyAbsCross](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_extendedChainFamilyAbsCross_eq
  [Fintype V]
  [DecidableEq V]
  [Fintype I]
  [DecidableEq I]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : I -> Nat -> V)
  (hinj : Function.Injective (fun q : I × Fin N => ginibreChainEdge (v q.1) q.2))
  (hedge : forall i (j : Fin N), ginibreChainEdge (v i) j ∈ E)
  (hunit : forall i (j : Fin N), J (ginibreChainEdge (v i) j) = 1)
  (hendInj : Function.Injective (fun z : I ⊕ I => match z with | .inl i => v i 0 | .inr i => v i N))
  (hplusTop : forall i, 1 <= hPlus (v i 0))
  (hmixTop : forall i, h (v i 0) = -hPlus (v i 0))
  (hplusBottom : forall i, 1 <= hPlus (v i N))
  (hmixBottom : forall i, h (v i N) = hPlus (v i N)) :
-- imply
  (∑ i : I, ((expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v i 0)) + expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v i 0))) + (∑ j : Fin N, |expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v i j.val)) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v i (j.val + 1))) - expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v i (j.val + 1))) * expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v i j.val))|) + (expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v i N)) - expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v i N))))) <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_extendedChainFamilyAbsCross E J hPlus h hJ hdom beta hbeta v N hinj hedge hunit hendInj hplusTop hmixTop hplusBottom hmixBottom

/--
[boundaryInterfaceFreeEnergy_deriv_ge_chain](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_chain_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
  {m : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : Nat -> V)
  (hinj : Function.Injective (ginibreChainEdge (N := N) v))
  (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
  (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
  (hconst : forall j, j <= N -> expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v j)) = m) :
-- imply
  m * (expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v N)) - expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v 0))) <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_chain E J hPlus h hJ hdom beta hbeta v N m hinj hedge hunit hconst

/--
[boundaryInterfaceFreeEnergy_deriv_ge_two_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma boundaryInterfaceFreeEnergy_deriv_ge_two_mul_sq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {beta : Real}
  {N : Nat}
  {m : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : forall e, e ∈ E -> 0 <= J e)
  (hdom : forall x, |h x| <= hPlus x)
  (hbeta : 0 <= beta)
  (v : Nat -> V)
  (hinj : Function.Injective (ginibreChainEdge (N := N) v))
  (hedge : forall j : Fin N, ginibreChainEdge v j ∈ E)
  (hunit : forall j : Fin N, J (ginibreChainEdge v j) = 1)
  (hconst : forall j, j <= N -> expJ E (fun e => beta * J e) (fun x => beta * hPlus x) (fun s => spin s (v j)) = m)
  (hbottom : expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v 0)) = -m)
  (htop : expJ E (fun e => beta * J e) (fun x => beta * h x) (fun s => spin s (v N)) = m) :
-- imply
  2 * m ^ 2 <= deriv (boundaryInterfaceFreeEnergy E J hPlus h) beta := by
-- proof
  apply StatMech.Ising.boundaryInterfaceFreeEnergy_deriv_ge_two_mul_sq E J hPlus h hJ hdom beta hbeta v N m hinj hedge hunit hconst hbottom htop

/--
[sum_fin_succ_sub_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma sum_fin_succ_sub_castSucc_eq
  [Fintype V]
  [DecidableEq V]
  {N : Nat}
-- given
  (q : Fin (N + 1) -> Real) :
-- imply
  (∑ j : Fin N, (q j.succ - q j.castSucc)) = q (Fin.last N) - q 0 := by
-- proof
  apply StatMech.Ising.sum_fin_succ_sub_castSucc N q

/--
[extendedChain_absCross_ge_two_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma extendedChain_absCross_ge_two_mul_sq_eq
  [Fintype V]
  [DecidableEq V]
  {N : Nat}
  {m : Real}
-- given
  (p q : Fin (N + 1) -> Real)
  (hm : 0 <= m)
  (hm1 : m <= 1)
  (hp : forall j, m <= p j)
  (hq : forall j, |q j| <= p j) :
-- imply
  2 * m ^ 2 <= (p 0 + q 0) + (∑ j : Fin N, |p j.castSucc * q j.succ - p j.succ * q j.castSucc|) + (p (Fin.last N) - q (Fin.last N)) := by
-- proof
  apply StatMech.Ising.extendedChain_absCross_ge_two_mul_sq N p q m hm hm1 hp hq

/--
[ginibre_chainCross_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma ginibre_chainCross_limit_eq
  [Fintype V]
  [DecidableEq V]
  {N : Nat}
  {Dlim : Real}
-- given
  (p q : Nat -> Fin (N + 1) -> Real)
  (pLim qLim : Fin (N + 1) -> Real)
  (D : Nat -> Real)
  (hp : forall j, Tendsto (fun k => p k j) atTop (nhds (pLim j)))
  (hq : forall j, Tendsto (fun k => q k j) atTop (nhds (qLim j)))
  (hD : Tendsto D atTop (nhds Dlim))
  (hcross : forall k, (∑ j : Fin N, (p k j.castSucc * q k j.succ - p k j.succ * q k j.castSucc)) <= D k) :
-- imply
  (∑ j : Fin N, (pLim j.castSucc * qLim j.succ - pLim j.succ * qLim j.castSucc)) <= Dlim := by
-- proof
  apply StatMech.Ising.ginibre_chainCross_limit N p q pLim qLim D Dlim hp hq hD hcross

/--
[ginibre_chainCross_limit_of_plus_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundaryDerivativeLower.lean)
-/
@[path]
private lemma ginibre_chainCross_limit_of_plus_const_eq
  [Fintype V]
  [DecidableEq V]
  {N : Nat}
  {m : Real}
  {Dlim : Real}
-- given
  (p q : Nat -> Fin (N + 1) -> Real)
  (qLim : Fin (N + 1) -> Real)
  (D : Nat -> Real)
  (hp : forall j, Tendsto (fun k => p k j) atTop (nhds m))
  (hq : forall j, Tendsto (fun k => q k j) atTop (nhds (qLim j)))
  (hD : Tendsto D atTop (nhds Dlim))
  (hcross : forall k, (∑ j : Fin N, (p k j.castSucc * q k j.succ - p k j.succ * q k j.castSucc)) <= D k) :
-- imply
  m * (qLim (Fin.last N) - qLim 0) <= Dlim := by
-- proof
  apply StatMech.Ising.ginibre_chainCross_limit_of_plus_const N p q qLim m D Dlim hp hq hD hcross


-- created on 2026-10-23
