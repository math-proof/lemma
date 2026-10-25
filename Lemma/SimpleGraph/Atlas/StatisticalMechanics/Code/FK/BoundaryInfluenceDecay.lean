import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.BoundaryInfluenceDecay.Part2
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fbd_sub_tendsto_zero_of_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_sub_tendsto_zero_of_eq_limit_eq
  {d : ℕ}
  {f g : ℕ → ℝ}
  {L : ℝ}
-- given
  (hf : Tendsto f atTop (𝓝 L))
  (hg : Tendsto g atTop (𝓝 L)) :
-- imply
  Tendsto (fun k => f k - g k) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_sub_tendsto_zero_of_eq_limit hf hg

/--
[fbd_sub_tendsto_zero_of_limits_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_sub_tendsto_zero_of_limits_eq_eq
  {d : ℕ}
  {f g : ℕ → ℝ}
  {L M : ℝ}
-- given
  (hf : Tendsto f atTop (𝓝 L))
  (hg : Tendsto g atTop (𝓝 M))
  (hLM : L = M) :
-- imply
  Tendsto (fun k => f k - g k) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_sub_tendsto_zero_of_limits_eq hf hg hLM

/--
[fbd_decay_of_wired_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_of_wired_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_of_wired_density_eq N eb eb' hp hp1 hdens

/--
[fbd_decay_of_free_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_of_free_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdens : freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb') p) :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_of_free_density_eq N eb eb' hp hp1 hdens

/--
[fbd_decay_cross_of_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_cross_of_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdens : wiredEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb') p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_cross_of_density_eq N eb eb' hp hp1 hdens

/--
[fbd_decay_boxSym_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_boxSym_wired_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_boxSym_wired S N eb hp hp1

/--
[fbd_decay_boxSym_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_boxSym_free_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_boxSym_free S N eb hp hp1

/--
[fbd_decay_interior_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_interior_at_continuity_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_interior_at_continuity N eb hsecant hpmem hcont

/--
[fbd_decay_cross_boxSym_at_continuity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_cross_boxSym_at_continuity_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hsecant : ∀ p ∈ Ioo (0:ℝ) 1, ∀ p' ∈ Ioo (0:ℝ) 1, p' < p → wiredEdgeDensity d 2 (edgeIncl d N eb) p' ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p)
  (hpmem : p ∈ Ioo (0:ℝ) 1)
  (hcont : ContinuousWithinAt (wiredEdgeDensity d 2 (edgeIncl d N eb)) (Ioo (0:ℝ) 1) p) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (Sym2.map (S.lift N) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_cross_boxSym_at_continuity S N eb hsecant hpmem hcont

/--
[fbd_centred_eq_translated_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_centred_eq_translated_wired_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d m)}
  {p q : ℝ} :
-- imply
  edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p q) eb = edgeMargProb (wiredFkProb (fvs_transBoxGraph d m v) (fvs_transBoxBoundary d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb) := by
-- proof
  apply StatMech.FK.fbd_centred_eq_translated_wired m v eb

/--
[fbd_centred_eq_translated_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_centred_eq_translated_free_eq
  {d : ℕ}
  {m : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d m)}
  {p q : ℝ} :
-- imply
  edgeMargProb (fkProb (boxGraph d m) p q) eb = edgeMargProb (fkProb (fvs_transBoxGraph d m v) p q) (Sym2.map (fvs_transEquiv d m v) eb) := by
-- proof
  apply StatMech.FK.fbd_centred_eq_translated_free m v eb

/--
[fbd_decay_translate_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_translate_wired_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d N)}
  {p q : ℝ} :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p q) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p q) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_translate_wired N v eb

/--
[fbd_decay_translate_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_translate_free_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb : Sym2 (boxVerts d N)}
  {p q : ℝ} :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p q) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (fvs_transBoxGraph d (N+k) v) p q) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb))) atTop (𝓝 0) := by
-- proof
  apply StatMech.FK.fbd_decay_translate_free N v eb

/--
[fbd_decay_iff_wired_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_iff_wired_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) ↔ wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.fbd_decay_iff_wired_density_eq N eb eb' hp hp1

/--
[fbd_decay_iff_free_density_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_decay_iff_free_density_eq_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) ↔ freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.fbd_decay_iff_free_density_eq N eb eb' hp hp1

/--
[fbd_wired_density_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_wired_density_translation_inv_eq
  {d : ℕ}
  {v x y : Site d}
  {p : ℝ}
  {N : ℕ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hx : x ∈ box d N)
  (hy : y ∈ box d N)
  (hx' : fktc_translate v x ∈ box d N)
  (hy' : fktc_translate v y ∈ box d N)
  (hdecay : Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy)) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
-- imply
  wiredEdgeDensity d 2 s(x, y) p = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
-- proof
  apply StatMech.FK.fbd_wired_density_translation_inv v x y hp hp1 N hx hy hx' hy' hdecay

/--
[fbd_wired_density_eq_of_offCentreCarrier](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/BoundaryInfluenceDecay.lean)
-/
@[path]
private lemma fbd_wired_density_eq_of_offCentreCarrier_eq
  {d : ℕ}
  {N : ℕ}
  {v : Site d}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcarrier : Tendsto (fbd_offCentreCarrier N v eb' p 2) atTop (𝓝 0))
  (htrans : ∀ k, edgeMargProb (wiredFkProb (fvs_transBoxGraph d (N+k) v) (fvs_transBoxBoundary d (N+k) v) p 2) (Sym2.map (fvs_transEquiv d (N+k) v) (innerEdgeLE d (Nat.le_add_right N k) eb')) = edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.fbd_wired_density_eq_of_offCentreCarrier N v eb eb' hp hp1 hcarrier htrans


-- created on 2026-10-23
