import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FK.TranslationCofinal
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[fktc_translate_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_translate_apply_eq
  {d : ℕ}
  {v x : Site d} :
-- imply
  fktc_translate v x = x + v := by
-- proof
  apply StatMech.FK.fktc_translate_apply v x

/--
[fktc_translate_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_translate_adj_eq
  {d : ℕ}
  {v : Site d}
  {x y : Site d} :
-- imply
  (hypercubicLattice d).Adj (fktc_translate v x) (fktc_translate v y) ↔ (hypercubicLattice d).Adj x y := by
-- proof
  apply StatMech.FK.fktc_translate_adj v x y

/--
[fktc_translate_not_box_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_translate_not_box_mem_eq
  {d : ℕ}
  {j : Fin d} :
-- imply
  ¬ (∀ n x, fktc_translate (fun i => if i = j then (1:ℤ) else 0) x ∈ box d n ↔ x ∈ box d n) := by
-- proof
  apply StatMech.FK.fktc_translate_not_box_mem j

/--
[fktc_point_and_translate_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_point_and_translate_in_box_eq
  {d : ℕ}
  {v x : Site d} :
-- imply
  ∃ N, x ∈ box d N ∧ fktc_translate v x ∈ box d N := by
-- proof
  apply StatMech.FK.fktc_point_and_translate_in_box v x

/--
[fktc_edge_and_translate_in_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_edge_and_translate_in_box_eq
  {d : ℕ}
  {v x y : Site d} :
-- imply
  ∃ N, x ∈ box d N ∧ y ∈ box d N ∧ fktc_translate v x ∈ box d N ∧ fktc_translate v y ∈ box d N := by
-- proof
  apply StatMech.FK.fktc_edge_and_translate_in_box v x y

/--
[fktc_translate_cofinal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_translate_cofinal_eq
  {d : ℕ}
  {v x y : Site d} :
-- imply
  ∃ N, x ∈ box d N ∧ y ∈ box d N ∧ fktc_translate v x ∈ box d N ∧ fktc_translate v y ∈ box d N := by
-- proof
  apply StatMech.FK.fktc_translate_cofinal v x y

/--
[fktc_edgeIncl_boxEdge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_edgeIncl_boxEdge_eq
  {d : ℕ}
  {N : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d N)
  (hy : y ∈ box d N) :
-- imply
  edgeIncl d N (fktc_boxEdge hx hy) = s(x, y) := by
-- proof
  apply StatMech.FK.fktc_edgeIncl_boxEdge hx hy

/--
[fktc_wired_density_eq_of_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_density_eq_of_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fktc_wired_density_eq_of_boxSym S N eb hp hp1

/--
[fktc_free_density_eq_of_boxSym](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_density_eq_of_boxSym_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N (Sym2.map (S.lift N) eb)) p := by
-- proof
  apply StatMech.FK.fktc_free_density_eq_of_boxSym S N eb hp hp1

/--
[fktc_wired_box_density_const_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_box_density_const_of_orbit_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
-- imply
  ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p := by
-- proof
  apply StatMech.FK.fktc_wired_box_density_const_of_orbit S N EB eb₀ hp hp1 horb

/--
[fktc_free_box_density_const_of_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_box_density_const_of_orbit_eq
  {d : ℕ}
  {S : BoxSym d}
  {N : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
-- imply
  ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
-- proof
  apply StatMech.FK.fktc_free_box_density_const_of_orbit S N EB eb₀ hp hp1 horb

/--
[fktc_wired_density_eq_of_marg_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_density_eq_of_marg_decay_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.fktc_wired_density_eq_of_marg_decay N eb eb' hp hp1 hdecay

/--
[fktc_free_density_eq_of_marg_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_density_eq_of_marg_decay_eq
  {d : ℕ}
  {N : ℕ}
  {eb eb' : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hdecay : Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb')) atTop (𝓝 0)) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb') p := by
-- proof
  apply StatMech.FK.fktc_free_density_eq_of_marg_decay N eb eb' hp hp1 hdecay

/--
[fktc_wired_density_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_density_translation_inv_eq
  {d : ℕ}
  {v x y : Site d}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N, ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N, Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy)) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
-- imply
  wiredEdgeDensity d 2 s(x, y) p = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
-- proof
  apply StatMech.FK.fktc_wired_density_translation_inv v x y hp hp1 hcof

/--
[fktc_free_density_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_density_translation_inv_eq
  {d : ℕ}
  {v x y : Site d}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcof : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N, ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N, Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy)) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
-- imply
  freeEdgeDensity d 2 s(x, y) p = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
-- proof
  apply StatMech.FK.fktc_free_density_translation_inv v x y hp hp1 hcof

/--
[fktc_density_translation_inv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_density_translation_inv_eq
  {d : ℕ}
  {v x y : Site d}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hcofW : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N, ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N, Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy)) - edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0))
  (hcofF : ∃ N, ∃ hx : x ∈ box d N, ∃ hy : y ∈ box d N, ∃ hx' : fktc_translate v x ∈ box d N, ∃ hy' : fktc_translate v y ∈ box d N, Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx hy)) - edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) (fktc_boxEdge hx' hy'))) atTop (𝓝 0)) :
-- imply
  wiredEdgeDensity d 2 s(x, y) p = wiredEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p ∧ freeEdgeDensity d 2 s(x, y) p = freeEdgeDensity d 2 s(fktc_translate v x, fktc_translate v y) p := by
-- proof
  apply StatMech.FK.fktc_density_translation_inv v x y hp hp1 hcofW hcofF

/--
[fktc_wired_density_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_density_eq_const_eq
  {d : ℕ}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hconst : ∀ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p = wiredEdgeDensity d 2 (edgeIncl d N eb₀) p)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.fktc_wired_density_eq_const N n hNn EB eb₀ hconst hp hp1

/--
[fktc_free_density_eq_const](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_density_eq_const_eq
  {d : ℕ}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hconst : ∀ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p = freeEdgeDensity d 2 (edgeIncl d N eb₀) p)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * fkProb (boxGraph d n) p 2 ω) ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
-- proof
  apply StatMech.FK.fktc_free_density_eq_const N n hNn EB eb₀ hconst hp hp1

/--
[fktc_wired_density_eq_const_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_wired_density_eq_const_orbit_eq
  {d : ℕ}
  {S : BoxSym d}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
-- imply
  (EB.card : ℝ) * wiredEdgeDensity d 2 (edgeIncl d N eb₀) p ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.fktc_wired_density_eq_const_orbit S N n hNn EB eb₀ hp hp1 horb

/--
[fktc_free_density_eq_const_orbit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/TranslationCofinal.lean)
-/
@[path]
private lemma fktc_free_density_eq_const_orbit_eq
  {d : ℕ}
  {S : BoxSym d}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {eb₀ : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1)
  (horb : ∀ eb ∈ EB, ∃ k : ℕ, eb = (Sym2.map (S.lift N))^[k] eb₀) :
-- imply
  (∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * fkProb (boxGraph d n) p 2 ω) ≤ (EB.card : ℝ) * freeEdgeDensity d 2 (edgeIncl d N eb₀) p := by
-- proof
  apply StatMech.FK.fktc_free_density_eq_const_orbit S N n hNn EB eb₀ hp hp1 horb


-- created on 2026-10-23
