import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.GinibreBoundary
open Finset StatMech StatMech.Ising


/--
[ginibre_crossWeight_factor](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_crossWeight_factor_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {a q : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real) :
-- imply
  wJ E J hPlus a * wJ E J h (xnor a q) = wJ E (fun e => J e * (1 + bond q e)) (fun v => hPlus v + h v * spin q v) a := by
-- proof
  apply StatMech.Ising.ginibre_crossWeight_factor E J hPlus h a q

/--
[ginibre_inducedField_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_inducedField_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {q : ConfigSpace V}
  {v : V}
-- given
  (hPlus h : V -> Real)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  0 <= hPlus v + h v * spin q v := by
-- proof
  apply StatMech.Ising.ginibre_inducedField_nonneg hPlus h hdom q v

/--
[ginibre_cross_inner_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_cross_inner_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y : V}
  {q : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  0 <= ∑ a : ConfigSpace V, wJ E J hPlus a * wJ E J h (xnor a q) * ((spin a x + spin (xnor a q) x) * (spin a y - spin (xnor a q) y)) := by
-- proof
  apply StatMech.Ising.ginibre_cross_inner_nonneg E J hPlus h hJ hdom x y q

/--
[ginibre_cross_numerator_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_cross_numerator_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  0 <= ∑ a : ConfigSpace V, ∑ b : ConfigSpace V, wJ E J hPlus a * wJ E J h b * ((spin a x + spin b x) * (spin a y - spin b y)) := by
-- proof
  apply StatMech.Ising.ginibre_cross_numerator_nonneg E J hPlus h hJ hdom x y

/--
[ginibre_boundary_correlation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_boundary_correlation_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  expJ E J hPlus (fun s => spin s x * spin s y) - expJ E J h (fun s => spin s x * spin s y) >= expJ E J hPlus (fun s => spin s x) * expJ E J h (fun s => spin s y) - expJ E J hPlus (fun s => spin s y) * expJ E J h (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_correlation E J hPlus h hJ hdom x y

/--
[ginibre_boundary_twoPoint_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_boundary_twoPoint_mono_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x y : V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  expJ E J h (fun s => spin s x * spin s y) <= expJ E J hPlus (fun s => spin s x * spin s y) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_twoPoint_mono E J hPlus h hJ hdom x y

/--
[ginibre_boundary_bond_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_boundary_bond_mono_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  expJ E J h (fun s => bond s e) <= expJ E J hPlus (fun s => bond s e) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_bond_mono E J hPlus h hJ hdom e

/--
[ginibre_cross_one_inner_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_cross_one_inner_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x : V}
  {epsilon : Real}
  {q : ConfigSpace V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (hepsilon : forall q : ConfigSpace V, 0 <= 1 + epsilon * spin q x) :
-- imply
  0 <= ∑ a : ConfigSpace V, wJ E J hPlus a * wJ E J h (xnor a q) * (spin a x + epsilon * spin (xnor a q) x) := by
-- proof
  apply StatMech.Ising.ginibre_cross_one_inner_nonneg E J hPlus h hJ hdom x epsilon hepsilon q

/--
[ginibre_boundary_onePoint_signed_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_boundary_onePoint_signed_nonneg_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x : V}
  {epsilon : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (hepsilon : forall q : ConfigSpace V, 0 <= 1 + epsilon * spin q x) :
-- imply
  0 <= expJ E J hPlus (fun s => spin s x) + epsilon * expJ E J h (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_onePoint_signed_nonneg E J hPlus h hJ hdom x epsilon hepsilon

/--
[ginibre_boundary_abs_onePoint_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_boundary_abs_onePoint_le_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {x : V}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v) :
-- imply
  |expJ E J h (fun s => spin s x)| <= expJ E J hPlus (fun s => spin s x) := by
-- proof
  apply StatMech.Ising.ginibre_boundary_abs_onePoint_le E J hPlus h hJ hdom x

/--
[ginibre_chain_correlation_telescope](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_chain_correlation_telescope_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {N : Nat}
  {m : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (v : Nat -> V)
  (hconst : forall j, j <= N -> expJ E J hPlus (fun s => spin s (v j)) = m) :
-- imply
  m * (expJ E J h (fun s => spin s (v N)) - expJ E J h (fun s => spin s (v 0))) <= ∑ j ∈ Finset.range N, (expJ E J hPlus (fun s => spin s (v j) * spin s (v (j + 1))) - expJ E J h (fun s => spin s (v j) * spin s (v (j + 1)))) := by
-- proof
  apply StatMech.Ising.ginibre_chain_correlation_telescope E J hPlus h hJ hdom v N m hconst

/--
[ginibre_chain_correlation_ge_two_mul_sq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/GinibreBoundary.lean)
-/
@[path]
private lemma ginibre_chain_correlation_ge_two_mul_sq_eq
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {N : Nat}
  {m : Real}
-- given
  (J : Sym2 V -> Real)
  (hPlus h : V -> Real)
  (hJ : ∀ e ∈ E, 0 <= J e)
  (hdom : forall v, |h v| <= hPlus v)
  (v : Nat -> V)
  (hconst : forall j, j <= N -> expJ E J hPlus (fun s => spin s (v j)) = m)
  (hbottom : expJ E J h (fun s => spin s (v 0)) = -m)
  (htop : expJ E J h (fun s => spin s (v N)) = m) :
-- imply
  2 * m ^ 2 <= ∑ j ∈ Finset.range N, (expJ E J hPlus (fun s => spin s (v j) * spin s (v (j + 1))) - expJ E J h (fun s => spin s (v j) * spin s (v (j + 1)))) := by
-- proof
  apply StatMech.Ising.ginibre_chain_correlation_ge_two_mul_sq E J hPlus h hJ hdom v N m hconst hbottom htop


-- created on 2026-10-23
