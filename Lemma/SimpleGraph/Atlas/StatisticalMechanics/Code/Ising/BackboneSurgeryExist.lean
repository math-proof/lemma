import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.BackboneSurgeryExist
open Finset Classical StatMech StatMech.Ising


/--
[bse_surgery_of_inj_zeroAllMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_surgery_of_inj_zeroAllMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
  {ι : Current V → Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hmem : ∀ m ∈ bbr_allFilter G M o x y, ι m ∈ bbr_noneFilter G M o x y)
  (hinj : ∀ m ∈ bbr_allFilter G M o x y, ∀ m' ∈ bbr_allFilter G M o x y, ι m = ι m' → m = m')
  (hzero : ∀ m ∈ bbr_allFilter G M o x y, hnw_mass G β J m A = 0) :
-- imply
  bbr_BackboneSurgery G β J M A o x y := by
-- proof
  apply StatMech.Ising.bse_surgery_of_inj_zeroAllMass G β J hβ hJ M A o x y ι hmem hinj hzero

/--
[bse_surgery_of_card_le_zeroAllMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_surgery_of_card_le_zeroAllMass_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hcard : (bbr_allFilter G M o x y).card ≤ (bbr_noneFilter G M o x y).card)
  (hzero : ∀ m ∈ bbr_allFilter G M o x y, hnw_mass G β J m A = 0) :
-- imply
  bbr_BackboneSurgery G β J M A o x y := by
-- proof
  apply StatMech.Ising.bse_surgery_of_card_le_zeroAllMass G β J hβ hJ M A o x y hcard hzero

/--
[bse_surgery_satisfiable_via](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_surgery_satisfiable_via_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hno : bbr_allFilter G M o x y = ∅) :
-- imply
  bbr_BackboneSurgery G β J M A o x y := by
-- proof
  apply StatMech.Ising.bse_surgery_satisfiable_via G β J hβ hJ M A o x y hno

/--
[bse_switching_fixes_m](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_switching_fixes_m_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {u v : V}
  {A : Finset V}
-- given
  (huv : u ≠ v)
  (hconn : connP (oddEdges G.edgeFinset m) u v) :
-- imply
  hnw_mass G β J m (A ∆ {u, v}) = hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bse_switching_fixes_m G β J m huv hconn A

/--
[bse_allMass_eq_self_paired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_allMass_eq_self_paired_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {o x y : V}
-- given
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_mass G β J m (A ∆ {x, y}) = hnw_mass G β J m A ∧ hnw_mass G β J m (A ∆ {o, y}) = hnw_mass G β J m A ∧ hnw_mass G β J m (A ∆ {o, x}) = hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bse_allMass_eq_self_paired G β J m A hox hoy hxy hall

/--
[bse_selfPairing_doubling_forces_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_selfPairing_doubling_forces_zero_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {A : Finset V}
  {o x y : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hall : hnw_allConn G m o x y)
  (hself : 2 * hnw_mass G β J m A ≤ hnw_mass G β J m (A ∆ {x, y})) :
-- imply
  hnw_mass G β J m A = 0 := by
-- proof
  apply StatMech.Ising.bse_selfPairing_doubling_forces_zero G β J hβ hJ m A hox hoy hxy hall hself

/--
[bse_addBackbone_leaves_family](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_addBackbone_leaves_family_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {A : Finset V}
  {x y : V}
  {P : Finset (Sym2 V)}
-- given
  (_hxy : x ≠ y)
  (hP : P ⊆ G.edgeFinset)
  (hsrcP : srcP P = {x, y})
  (hm : Sharpness.sources G m = A) :
-- imply
  Sharpness.sources G (fun e => m e + (if e ∈ P then 1 else 0)) ≠ A := by
-- proof
  apply StatMech.Ising.bse_addBackbone_leaves_family G m A _hxy P hP hsrcP hm

/--
[bse_addBackbone_weight_not_doubling](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryExist.lean)
-/
@[path]
private lemma bse_addBackbone_weight_not_doubling_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V} :
-- imply
  Sharpness.weight G β J (fun e => m e + (if e ∈ (∅ : Finset (Sym2 V)) then 1 else 0)) = Sharpness.weight G β J m := by
-- proof
  apply StatMech.Ising.bse_addBackbone_weight_not_doubling G β J m


-- created on 2026-10-23
