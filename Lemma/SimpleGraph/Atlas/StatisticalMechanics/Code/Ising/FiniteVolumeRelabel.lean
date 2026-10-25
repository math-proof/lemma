import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Ising.FiniteVolumeRelabel
open Finset StatMech StatMech.Ising


/--
[isingCfgEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingCfgEquiv_apply_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
  {x : V} :
-- imply
  isingCfgEquiv σ ω x = ω (σ x) := by
-- proof
  apply StatMech.Ising.isingCfgEquiv_apply σ ω x

/--
[spin_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma spin_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
  {x : V} :
-- imply
  spin (isingCfgEquiv σ ω) x = spin ω (σ x) := by
-- proof
  apply StatMech.Ising.spin_isingCfgEquiv σ ω x

/--
[spinProd_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma spinProd_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
  {A : Finset V} :
-- imply
  spinProd A (isingCfgEquiv σ ω) = spinProd (A.map σ.toEmbedding) ω := by
-- proof
  apply StatMech.Ising.spinProd_isingCfgEquiv σ ω A

/--
[bond_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma bond_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
  {e : Sym2 V} :
-- imply
  bond (isingCfgEquiv σ ω) e = bond ω (Sym2.map σ e) := by
-- proof
  apply StatMech.Ising.bond_isingCfgEquiv σ ω e

/--
[sum_bond_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma sum_bond_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y)) :
-- imply
  (∑ e ∈ G.edgeFinset, bond (isingCfgEquiv σ ω) e) = ∑ e ∈ H.edgeFinset, bond ω e := by
-- proof
  apply StatMech.Ising.sum_bond_isingCfgEquiv G H σ hσ ω

/--
[sum_spin_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma sum_spin_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace W} :
-- imply
  (∑ x : V, spin (isingCfgEquiv σ ω) x) = ∑ y : W, spin ω y := by
-- proof
  apply StatMech.Ising.sum_spin_isingCfgEquiv G H σ ω

/--
[hamiltonian_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma hamiltonian_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (h : ℝ) :
-- imply
  hamiltonian G h (isingCfgEquiv σ ω) = hamiltonian H h ω := by
-- proof
  apply StatMech.Ising.hamiltonian_isingCfgEquiv G H σ hσ h ω

/--
[isingWeight_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingWeight_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : ℝ) :
-- imply
  isingWeight G β h (isingCfgEquiv σ ω) = isingWeight H β h ω := by
-- proof
  apply StatMech.Ising.isingWeight_isingCfgEquiv G H σ hσ β h ω

/--
[isingZ_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingZ_relabel_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : ℝ) :
-- imply
  isingZ G β h = isingZ H β h := by
-- proof
  apply StatMech.Ising.isingZ_relabel G H σ hσ β h

/--
[isingProb_isingCfgEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingProb_isingCfgEquiv_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {ω : ConfigSpace W}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : ℝ) :
-- imply
  isingProb G β h (isingCfgEquiv σ ω) = isingProb H β h ω := by
-- proof
  apply StatMech.Ising.isingProb_isingCfgEquiv G H σ hσ β h ω

/--
[isingExpectation_spin_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingExpectation_spin_relabel_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {x : V}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : ℝ) :
-- imply
  isingExpectation G β h (fun ω => spin ω x) = isingExpectation H β h (fun ω => spin ω (σ x)) := by
-- proof
  apply StatMech.Ising.isingExpectation_spin_relabel G H σ hσ β h x

/--
[isingExpectation_spinProd_relabel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/FiniteVolumeRelabel.lean)
-/
@[path]
private lemma isingExpectation_spinProd_relabel_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {H : SimpleGraph W}
  [DecidableRel H.Adj]
  {σ : V ≃ W}
  {A : Finset V}
-- given
  (hσ : ∀ x y, G.Adj x y ↔ H.Adj (σ x) (σ y))
  (β h : ℝ) :
-- imply
  isingExpectation G β h (spinProd A) = isingExpectation H β h (spinProd (A.map σ.toEmbedding)) := by
-- proof
  apply StatMech.Ising.isingExpectation_spinProd_relabel G H σ hσ β h A


-- created on 2026-10-23
