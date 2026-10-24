import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Ising.HdomMultiplicity
open Finset Classical StatMech StatMech.Ising


/--
[hmu_addBackbone_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_apply_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {P : Finset (Sym2 V)}
  {m : Current V}
  {e : Sym2 V} :
-- imply
  hmu_addBackbone P m e = m e + (if e ∈ P then 1 else 0) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_apply G P m e

/--
[hmu_addBackbone_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_injective_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {P : Finset (Sym2 V)} :
-- imply
  Function.Injective (hmu_addBackbone (V := V) P) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_injective G P

/--
[hmu_addBackbone_even_on](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_even_on_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (hPodd : ∀ e ∈ P, Odd (m e))
  (he : e ∈ P) :
-- imply
  Even (hmu_addBackbone P m e) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_even_on G m P hPodd he

/--
[hmu_addBackbone_oddEdges_disjoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_oddEdges_disjoint_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)}
-- given
  (hPodd : ∀ e ∈ P, Odd (m e)) :
-- imply
  Disjoint (oddEdges G.edgeFinset (hmu_addBackbone P m)) P := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_oddEdges_disjoint G m P hPodd

/--
[hmu_addBackbone_oddEdges_off](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_oddEdges_off_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)}
  {e : Sym2 V}
-- given
  (he : e ∉ P) :
-- imply
  Odd (hmu_addBackbone P m e) ↔ Odd (m e) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_oddEdges_off G m P he

/--
[hmu_addBackbone_posEdges_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_posEdges_mono_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)} :
-- imply
  posEdges G.edgeFinset m ⊆ posEdges G.edgeFinset (hmu_addBackbone P m) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_posEdges_mono G m P

/--
[hmu_addBackbone_connPos_preserved](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_connPos_preserved_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {m : Current V}
  {P : Finset (Sym2 V)}
  {u v : V}
-- given
  (h : connP (posEdges G.edgeFinset m) u v) :
-- imply
  connP (posEdges G.edgeFinset (hmu_addBackbone P m)) u v := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_connPos_preserved G m P h

/--
[hmu_addBackbone_weight_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_addBackbone_weight_ratio_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
  {P : Finset (Sym2 V)} :
-- imply
  Sharpness.weight G β J (hmu_addBackbone P m) = Sharpness.weight G β J m * ∏ e ∈ G.edgeFinset, (if e ∈ P then (β * J e) / (m e + 1) else 1) := by
-- proof
  apply StatMech.Ising.hmu_addBackbone_weight_ratio G β J m P

/--
[hmu_weight_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_weight_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
-- given
  (hβ : 0 < β)
  (hJ : ∀ e, 0 < J e) :
-- imply
  0 < Sharpness.weight G β J m := by
-- proof
  apply StatMech.Ising.hmu_weight_pos G β J hβ hJ m

/--
[hmu_mass_ge_weight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_mass_ge_weight_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
-- given
  (hβ : 0 ≤ β)
  (hJ : ∀ e, 0 ≤ J e) :
-- imply
  Sharpness.weight G β J m ≤ hnw_mass G β J m (Sharpness.sources G m) := by
-- proof
  apply StatMech.Ising.hmu_mass_ge_weight G β J hβ hJ m

/--
[hmu_mass_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_mass_pos_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {β : ℝ}
  {J : Sym2 V → ℝ}
  {m : Current V}
-- given
  (hβ : 0 < β)
  (hJ : ∀ e, 0 < J e) :
-- imply
  0 < hnw_mass G β J m (Sharpness.sources G m) := by
-- proof
  apply StatMech.Ising.hmu_mass_pos G β J hβ hJ m

/--
[hmu_tri_conn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_tri_conn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {a b : Fin 3}
-- given
  (hab : a ≠ b) :
-- imply
  connP (oddEdges (hmu_TriG.edgeFinset) hmu_triM) a b := by
-- proof
  apply StatMech.Ising.hmu_tri_conn G a b hab

/--
[hmu_tri_allConn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_tri_allConn_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  hnw_allConn hmu_TriG hmu_triM 0 1 2 := by
-- proof
  apply StatMech.Ising.hmu_tri_allConn G

/--
[hmu_tri_src](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_tri_src_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  Sharpness.sources hmu_TriG hmu_triM = (∅ : Finset (Fin 3)) := by
-- proof
  apply StatMech.Ising.hmu_tri_src G

/--
[hmu_hdom_refutable](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Ising/HdomMultiplicity.lean)
-/
@[path]
private lemma hmu_hdom_refutable_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj] :
-- imply
  ¬ (2 * (∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_allConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) ≤ ∑ m ∈ ({hmu_triM} : Finset (Current (Fin 3))).filter (fun m => hnw_noneConn hmu_TriG m 0 1 2), hnw_mass hmu_TriG 1 (fun _ => 1) m ∅) := by
-- proof
  apply StatMech.Ising.hmu_hdom_refutable G


-- created on 2026-10-23
