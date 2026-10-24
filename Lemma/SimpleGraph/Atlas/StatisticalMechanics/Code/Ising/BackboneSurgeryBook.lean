import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.BackboneSurgeryBook
open Finset Classical StatMech StatMech.Ising


/--
[bsb_BackboneSurgery_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryBook.lean)
-/
@[path]
private lemma bsb_BackboneSurgery_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ bbr_BackboneSurgery hmu_TriG 1 (fun _ => 1) ({hmu_triM} : Finset (Current (Fin 3))) ∅ 0 1 2 := by
-- proof
  apply StatMech.Ising.bsb_BackboneSurgery_refutable G

/--
[bsb_gap_allConn_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryBook.lean)
-/
@[path]
private lemma bsb_gap_allConn_nonpos_eq
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
  (hall : hnw_allConn G m o x y) :
-- imply
  hnw_gap G β J m A o x y ≤ 0 := by
-- proof
  apply StatMech.Ising.bsb_gap_allConn_nonpos G β J hβ hJ m A hox hoy hxy hall

/--
[bsb_pairwise_switching_dom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryBook.lean)
-/
@[path]
private lemma bsb_pairwise_switching_dom_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {M : Finset (Current V)}
  {A : Finset V}
  {u v : V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e)
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (huv : u ≠ v)
  (hcoh : ∀ m ∈ M, connP (oddEdges G.edgeFinset m) u v ↔ connP (posEdges G.edgeFinset m) u v) :
-- imply
  ∑ m ∈ M, hnw_mass G β J m (A ∆ {u, v}) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bsb_pairwise_switching_dom G β J hβ hJ M hnd A hm huv hcoh

/--
[bsb_ghs_singlePair_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryBook.lean)
-/
@[path]
private lemma bsb_ghs_singlePair_le_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y) :
-- imply
  (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A) ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y}) ≤ ∑ m ∈ M, hnw_mass G β J m A) ∧ (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x}) ≤ ∑ m ∈ M, hnw_mass G β J m A) := by
-- proof
  apply StatMech.Ising.bsb_ghs_singlePair_le G β J hβ hJ M hnd A hm hox hoy hxy hcoh

/--
[bsb_ghs_of_hdom](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/BackboneSurgeryBook.lean)
-/
@[path]
private lemma bsb_ghs_of_hdom_eq
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
  (hnd : ∀ m ∈ M, ∀ e ∈ G.edgeFinset, ¬ e.IsDiag)
  (hm : ∀ m ∈ M, Sharpness.sources G m = A)
  (hox : o ≠ x)
  (hoy : o ≠ y)
  (hxy : x ≠ y)
  (hcoh : ∀ m ∈ M, hnw_coherent G m o x y)
  (hdom : 2 * (∑ m ∈ M.filter (fun m => hnw_allConn G m o x y), hnw_mass G β J m A) ≤ ∑ m ∈ M.filter (fun m => hnw_noneConn G m o x y), hnw_mass G β J m A) :
-- imply
  (∑ m ∈ M, hnw_mass G β J m (A ∆ {x, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, y})) + (∑ m ∈ M, hnw_mass G β J m (A ∆ {o, x})) ≤ ∑ m ∈ M, hnw_mass G β J m A := by
-- proof
  apply StatMech.Ising.bsb_ghs_of_hdom G β J M hnd A hm hox hoy hxy hcoh hdom


-- created on 2026-10-23
