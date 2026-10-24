import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.RotationInvariance
open MeasureTheory Filter Topology SimpleGraph Set StatMech.ConfigSpace StatMech.Lattice StatMech StatMech.FK


/--
[rot_permEquiv_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_permEquiv_apply_eq
  {d : ℕ}
  {d : ℕ}
  {π : Equiv.Perm (Fin d)}
  {x : Site d}
  {i : Fin d} :
-- imply
  rot_permEquiv d π x i = x (π.symm i) := by
-- proof
  apply StatMech.FK.rot_permEquiv_apply d π x i

/--
[rot_lift_edgeIncl](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_lift_edgeIncl_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)} :
-- imply
  edgeIncl d N (Sym2.map (S.lift N) eb) = Sym2.map S.τ (edgeIncl d N eb) := by
-- proof
  apply StatMech.FK.rot_lift_edgeIncl S N eb

/--
[rot_site_mem_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_site_mem_box_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  x ∈ box d (Finset.univ.sup (fun i => (x i).natAbs)) := by
-- proof
  apply StatMech.FK.rot_site_mem_box x

/--
[rot_free_density_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_free_density_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {e : Sym2 (Site d)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (Sym2.map S.τ e) p = freeEdgeDensity d 2 e p := by
-- proof
  apply StatMech.FK.rot_free_density_boxSym S e hp hp1

/--
[rot_wired_density_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wired_density_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {e : Sym2 (Site d)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (Sym2.map S.τ e) p = wiredEdgeDensity d 2 e p := by
-- proof
  apply StatMech.FK.rot_wired_density_boxSym S e hp hp1

/--
[rot_free_density_recentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_free_density_recentre_eq
  {d : ℕ}
  {x y : Site d}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
-- proof
  apply StatMech.FK.rot_free_density_recentre x y hp hp1

/--
[rot_wired_density_recentre](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wired_density_recentre_eq
  {d : ℕ}
  {x y : Site d}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d 2 (s((0 : Site d), y - x) : Sym2 (Site d)) p := by
-- proof
  apply StatMech.FK.rot_wired_density_recentre x y hp hp1

/--
[rot_candMap_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_candMap_apply_eq
  {d : ℕ}
  {j : Fin d}
  {b : Bool}
  {i : Fin d} :
-- imply
  candMap d (0 : Site d) (j, b) i = (if i = j then (if b then 1 else -1) else 0) := by
-- proof
  apply StatMech.FK.rot_candMap_apply j b i

/--
[rot_boxSym_fixes_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_boxSym_fixes_zero_eq
  {d : ℕ}
  {S : BoxSym d} :
-- imply
  S.τ (0 : Site d) = 0 := by
-- proof
  apply StatMech.FK.rot_boxSym_fixes_zero S

/--
[rot_signFlip_neg_to_pos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_signFlip_neg_to_pos_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  (fkTI_signFlip d j).τ (candMap d (0 : Site d) (j, false)) = candMap d (0 : Site d) (j, true) := by
-- proof
  apply StatMech.FK.rot_signFlip_neg_to_pos j

/--
[rot_permEquiv_axis_to_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_permEquiv_axis_to_zero_eq
  {d : ℕ}
  {j : Fin d}
-- given
  (hd : 0 < d) :
-- imply
  rot_permEquiv d (Equiv.swap (⟨0, hd⟩ : Fin d) j) (candMap d (0 : Site d) (j, true)) = candMap d (0 : Site d) (⟨0, hd⟩, true) := by
-- proof
  apply StatMech.FK.rot_permEquiv_axis_to_zero j hd

/--
[rot_map_centred_edge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_map_centred_edge_eq
  {d : ℕ}
  {S : BoxSym d}
  {w : Site d} :
-- imply
  Sym2.map S.τ (s((0 : Site d), w) : Sym2 (Site d)) = s((0 : Site d), S.τ w) := by
-- proof
  apply StatMech.FK.rot_map_centred_edge S w

/--
[rot_free_centred_unit_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_free_centred_unit_const_eq
  {d : ℕ}
  {j : Fin d}
  {b : Bool}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_free_centred_unit_const hd j b hp hp1

/--
[rot_wired_centred_unit_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wired_centred_unit_const_eq
  {d : ℕ}
  {j : Fin d}
  {b : Bool}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (s((0 : Site d), candMap d (0 : Site d) (j, b)) : Sym2 (Site d)) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_wired_centred_unit_const hd j b hp hp1

/--
[rot_edge_dir](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_edge_dir_eq
  {d : ℕ}
  {x y : Site d}
-- given
  (hadj : (hypercubicLattice d).Adj x y) :
-- imply
  ∃ p : Fin d × Bool, y - x = candMap d (0 : Site d) p := by
-- proof
  apply StatMech.FK.rot_edge_dir x y hadj

/--
[rot_free_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_free_edge_const_eq
  {d : ℕ}
  {x y : Site d}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (hadj : (hypercubicLattice d).Adj x y)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_free_edge_const hd x y hadj hp hp1

/--
[rot_wired_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wired_edge_const_eq
  {d : ℕ}
  {x y : Site d}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (hadj : (hypercubicLattice d).Adj x y)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (s(x, y) : Sym2 (Site d)) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_wired_edge_const hd x y hadj hp hp1

/--
[rot_free_box_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_free_box_edge_const_eq
  {d : ℕ}
  {m : ℕ}
  {eb : Sym2 (boxVerts d m)}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d m eb) p = freeEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_free_box_edge_const hd m eb heb hp hp1

/--
[rot_wired_box_edge_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wired_box_edge_const_eq
  {d : ℕ}
  {m : ℕ}
  {eb : Sym2 (boxVerts d m)}
  {p : ℝ}
-- given
  (hd : 0 < d)
  (heb : eb ∈ (boxGraph d m).edgeFinset)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d m eb) p = wiredEdgeDensity d 2 (rot_refUnitEdge d hd) p := by
-- proof
  apply StatMech.FK.rot_wired_box_edge_const hd m eb heb hp hp1

/--
[rot_freeRotationResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_freeRotationResidue_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (he' : e' ∈ (boxGraph d N).edgeFinset) :
-- imply
  ocs_FreeRotationResidue (d := d) N e' t := by
-- proof
  apply StatMech.FK.rot_freeRotationResidue hd N e' he' t

/--
[rot_wiredRotationResidue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wiredRotationResidue_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (he' : e' ∈ (boxGraph d N).edgeFinset) :
-- imply
  ocs_WiredRotationResidue (d := d) N e' t := by
-- proof
  apply StatMech.FK.rot_wiredRotationResidue hd N e' he' t

/--
[rot_freeRotationResidue_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_freeRotationResidue_edges_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (he' : e' ∈ (boxGraph d N).edgeFinset) :
-- imply
  ocs_FreeRotationResidue (d := d) N e' t := by
-- proof
  apply StatMech.FK.rot_freeRotationResidue_edges hd N e' he' t

/--
[rot_wiredRotationResidue_edges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_wiredRotationResidue_edges_eq
  {d : ℕ}
  {N : ℕ}
  {e' : Sym2 (boxVerts d N)}
  {t : ℝ}
-- given
  (hd : 0 < d)
  (he' : e' ∈ (boxGraph d N).edgeFinset) :
-- imply
  ocs_WiredRotationResidue (d := d) N e' t := by
-- proof
  apply StatMech.FK.rot_wiredRotationResidue_edges hd N e' he' t

/--
[rot_fk_uniqueness_of_diag](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/RotationInvariance.lean)
-/
@[path]
private lemma rot_fk_uniqueness_of_diag_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {g : ℝ → ℝ}
-- given
  (hd : 1 ≤ d)
  (hEbox : ∀ n, 0 < (boxGraph d n).edgeFinset.card)
  (hg : ConvexOn ℝ univ g)
  (hboxfree : ∀ t, Tendsto (fun n => ivp2_tiltFreeEnergy (boxGraph d n) 2 t) atTop (𝓝 (g t)))
  (hfreeDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset → ∀ (t : ℝ), ocs_FreeRotationResidue (d := d) N e' t)
  (hwiredDiag : ∀ (e' : Sym2 (boxVerts d N)), e' ∉ (boxGraph d N).edgeFinset → ∀ (t : ℝ), ocs_WiredRotationResidue (d := d) N e' t) :
-- imply
  {t : ℝ | ∃ A : Set (ConfigSpace (Sym2 (boxVerts d N))), IsIncreasing A ∧ eventMassProb (fuc_freeMass d N t) A ≠ eventMassProb (fuc_wiredMass d N t) A}.Countable := by
-- proof
  apply StatMech.FK.rot_fk_uniqueness_of_diag hd N eb hEbox hg hboxfree hfreeDiag hwiredDiag


-- created on 2026-10-23
