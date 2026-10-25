import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.DensityFiniteToInfinite.Part2
open MeasureTheory Filter Topology SimpleGraph Set StatMech StatMech.FK


/--
[dfi_indicator_boxEdgeOpenEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_indicator_boxEdgeOpenEvent_eq
  {d : ℕ}
  {m : ℕ}
  {e : Sym2 (boxVerts d m)}
  {ω : ConfigSpace (Sym2 (boxVerts d m))} :
-- imply
  (boxEdgeOpenEvent d m e).indicator (fun _ => (1:ℝ)) ω = (if ω e then (1:ℝ) else 0) := by
-- proof
  apply StatMech.FK.dfi_indicator_boxEdgeOpenEvent m e ω

/--
[dfi_wired_finite_mass_eq_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_wired_finite_mass_eq_edgeMarg_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = edgeMargProb (wiredFkProb (boxGraph d m) (boxBoundary d m) p 2) (innerEdgeLE d hNm eb) := by
-- proof
  apply StatMech.FK.dfi_wired_finite_mass_eq_edgeMarg N m hNm eb hp hp1

/--
[dfi_free_finite_mass_eq_edgeMarg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_free_finite_mass_eq_edgeMarg_eq
  {d : ℕ}
  {N m : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (freeFiniteMeasure d m hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxRestrict d N ⁻¹' (boxEdgeOpenEvent d N eb)) = edgeMargProb (fkProb (boxGraph d m) p 2) (innerEdgeLE d hNm eb) := by
-- proof
  apply StatMech.FK.dfi_free_finite_mass_eq_edgeMarg N m hNm eb hp hp1

/--
[dfi_tendsto_add_left](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_tendsto_add_left_eq
  {d : ℕ}
  {N : ℕ} :
-- imply
  Tendsto (fun k => N + k) atTop atTop := by
-- proof
  apply StatMech.FK.dfi_tendsto_add_left N

/--
[dfi_wired_density_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_wired_density_eq_limit_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (wiredFkProb (boxGraph d (N+k)) (boxBoundary d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (wiredEdgeDensity d 2 (edgeIncl d N eb) p)) := by
-- proof
  apply StatMech.FK.dfi_wired_density_eq_limit N eb hp hp1

/--
[dfi_free_density_eq_limit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_free_density_eq_limit_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  Tendsto (fun k => edgeMargProb (fkProb (boxGraph d (N+k)) p 2) (innerEdgeLE d (Nat.le_add_right N k) eb)) atTop (𝓝 (freeEdgeDensity d 2 (edgeIncl d N eb) p)) := by
-- proof
  apply StatMech.FK.dfi_free_density_eq_limit N eb hp hp1

/--
[dfi_wired_per_edge_ge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_wired_per_edge_ge_eq
  {d : ℕ}
  {N n : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  wiredEdgeDensity d 2 (edgeIncl d N eb) p ≤ edgeMargProb (wiredFkProb (boxGraph d n) (boxBoundary d n) p 2) (innerEdgeLE d hNn eb) := by
-- proof
  apply StatMech.FK.dfi_wired_per_edge_ge N n hNn eb hp hp1

/--
[dfi_freeEdgeDensity_eq_fkFreeLimitValue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_freeEdgeDensity_eq_fkFreeLimitValue_eq
  {d : ℕ}
  {N : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  freeEdgeDensity d 2 (edgeIncl d N eb) p = fkFreeLimitValue N hp hp1 (boxEdgeOpenEvent d N eb) := by
-- proof
  apply StatMech.FK.dfi_freeEdgeDensity_eq_fkFreeLimitValue N eb hp hp1

/--
[dfi_free_per_edge_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_free_per_edge_le_eq
  {d : ℕ}
  {N n : ℕ}
  {eb : Sym2 (boxVerts d N)}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  edgeMargProb (fkProb (boxGraph d n) p 2) (innerEdgeLE d hNn eb) ≤ freeEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.dfi_free_per_edge_le N n hNn eb hp hp1

/--
[dfi_openEdgeCount_expect](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_openEdgeCount_expect_eq
  {d : ℕ}
  [Fintype V]
  [DecidableEq V]
  {E : Finset (Sym2 V)}
  {μ : ConfigSpace (Sym2 V) → ℝ} :
-- imply
  (∑ ω : ConfigSpace (Sym2 V), dfi_openEdgeCount E ω * μ ω) = ∑ e ∈ E, edgeMargProb μ e := by
-- proof
  apply StatMech.FK.dfi_openEdgeCount_expect E μ

/--
[dfi_boxVertInclLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_boxVertInclLE_injective_eq
  {d : ℕ}
  {d : ℕ}
  {N n : ℕ}
-- given
  (hNn : N ≤ n) :
-- imply
  Function.Injective (boxVertInclLE d hNn) := by
-- proof
  apply StatMech.FK.dfi_boxVertInclLE_injective d hNn

/--
[dfi_innerEdgeLE_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_innerEdgeLE_injective_eq
  {d : ℕ}
  {d : ℕ}
  {N n : ℕ}
-- given
  (hNn : N ≤ n) :
-- imply
  Function.Injective (innerEdgeLE d hNn) := by
-- proof
  apply StatMech.FK.dfi_innerEdgeLE_injective d hNn

/--
[dfi_box_density_bound_wired](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_box_density_bound_wired_eq
  {d : ℕ}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ eb ∈ EB, wiredEdgeDensity d 2 (edgeIncl d N eb) p) ≤ ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.dfi_box_density_bound_wired N n hNn EB hp hp1

/--
[dfi_box_density_bound_free](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/DensityFiniteToInfinite.lean)
-/
@[path]
private lemma dfi_box_density_bound_free_eq
  {d : ℕ}
  {N n : ℕ}
  {EB : Finset (Sym2 (boxVerts d N))}
  {p : ℝ}
-- given
  (hNn : N ≤ n)
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ ω : ConfigSpace (Sym2 (boxVerts d n)), dfi_openEdgeCount (EB.image (innerEdgeLE d hNn)) ω * fkProb (boxGraph d n) p 2 ω) ≤ ∑ eb ∈ EB, freeEdgeDensity d 2 (edgeIncl d N eb) p := by
-- proof
  apply StatMech.FK.dfi_box_density_bound_free N n hNn EB hp hp1


-- created on 2026-10-23
