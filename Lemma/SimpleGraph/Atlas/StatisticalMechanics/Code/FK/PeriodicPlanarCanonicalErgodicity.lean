import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PeriodicPlanarCanonicalErgodicity.Part3
open MeasureTheory ProbabilityTheory Set Filter Topology StatMech StatMech.FK StatMech.FK.PeriodicPlanar


/--
[PeriodicGraph.bufferedEdgeWindow_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma bufferedEdgeWindow_mono_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V} :
-- imply
  Monotone P.bufferedEdgeWindow := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedEdgeWindow_mono P

/--
[PeriodicGraph.bufferedAdjMatchLE](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma bufferedAdjMatchLE_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N M : ℕ}
-- given
  (hNM : N ≤ M) :
-- imply
  ocd_AdjMatch (P.bufferedGraph N) (P.bufferedGraph M) (P.bufferedVertexInclLE hNM) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedAdjMatchLE P hNM

/--
[PeriodicGraph.edgeIncl_mem_bufferedEdgeWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma edgeIncl_mem_bufferedEdgeWindow_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {e : Sym2 (P.BufferedVertex N)} :
-- imply
  P.edgeIncl (P.bufferedRadius N) e ∈ P.bufferedEdgeWindow N := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.edgeIncl_mem_bufferedEdgeWindow P N e

/--
[PeriodicGraph.edgeIncl_range_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma edgeIncl_range_mono_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N M : ℕ}
  {e : Sym2 V}
-- given
  (hNM : N ≤ M)
  (he : e ∈ Set.range (P.edgeIncl (P.bufferedRadius N))) :
-- imply
  e ∈ Set.range (P.edgeIncl (P.bufferedRadius M)) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.edgeIncl_range_mono P hNM he

/--
[PeriodicGraph.isClopen_eq_bufferedCylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma isClopen_eq_bufferedCylinder_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {A : Set (ConfigSpace (Sym2 V))}
-- given
  (hA : IsClopen A) :
-- imply
  ∃ (N : ℕ) (S : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))), A = P.bufferedCylinder N S ∧ (IsIncreasing A → IsIncreasing S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.isClopen_eq_bufferedCylinder P A hA

/--
[PeriodicGraph.freeBufferedMeasure_inner_mul_exterior_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedMeasure_inner_mul_exterior_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N m : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
  {F : Finset (Sym2 V)}
  {S : Set (ConfigSpace F)}
-- given
  (hNm : N ≤ m)
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hF : (↑F : Set (Sym2 V)) ⊆ (P.bufferedEdgeWindow N)ᶜ)
  (hrange : ∀ e ∈ F, e ∈ Set.range (P.edgeIncl (P.bufferedRadius m))) :
-- imply
  (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A) * (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (cylinder (α := fun _ : Sym2 V => Bool) F S) ≤ (P.freeBufferedMeasure m hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A ∩ cylinder (α := fun _ : Sym2 V => Bool) F S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedMeasure_inner_mul_exterior_le P hNm hp hp1 hq hA F S hF hrange

/--
[PeriodicGraph.freeBufferedFinite_inner_mul_exteriorCylinder_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedFinite_inner_mul_exteriorCylinder_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
  {F : Finset (Sym2 V)}
  {S : Set (ConfigSpace F)}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hF : (↑F : Set (Sym2 V)) ⊆ (P.bufferedEdgeWindow N)ᶜ) :
-- imply
  (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A) * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (cylinder (α := fun _ : Sym2 V => Bool) F S) ≤ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A ∩ cylinder (α := fun _ : Sym2 V => Bool) F S) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedFinite_inner_mul_exteriorCylinder_le P N hp hp1 hq hA F S hF

/--
[PeriodicGraph.freeBufferedFinite_inner_mul_exterior_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedFinite_inner_mul_exterior_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {p q : ℝ}
  {A : Set (ConfigSpace (Sym2 (P.BufferedVertex N)))}
  {s : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hA : IsIncreasing A)
  (hs : @MeasurableSet _ (outsideSigma (P.bufferedEdgeWindow N)) s) :
-- imply
  (P.freeBufferedMeasure N hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A) * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (P.bufferedCylinder N A ∩ s) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedFinite_inner_mul_exterior_le P N hp hp1 hq hA hs

/--
[PeriodicGraph.freeBufferedInfiniteVolume_tail_clopen_product_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_tail_clopen_product_le_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {A s : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hAclopen : IsClopen A)
  (hAinc : IsIncreasing A)
  (hs : P.IsBufferedTailEvent s) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real A * (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real s ≤ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _).real (A ∩ s) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_tail_clopen_product_le P hp hp1 hq hAclopen hAinc hs

/--
[PeriodicGraph.freeBufferedInfiniteVolume_le_cond_tail_clopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_le_cond_tail_clopen_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {s : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hs : P.IsBufferedTailEvent s)
  (hs0 : (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) s ≠ 0) :
-- imply
  Ising.StochasticallyDominatedClopen (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) (((P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _))[|s]) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_le_cond_tail_clopen P hp hp1 hq hs hs0

/--
[PeriodicGraph.freeBufferedInfiniteVolume_tail_trivial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_tail_trivial_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {p q : ℝ}
  {s : Set (ConfigSpace (Sym2 V))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q)
  (hs : P.IsBufferedTailEvent s) :
-- imply
  (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 0 ∨ (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) s = 1 := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.freeBufferedInfiniteVolume_tail_trivial P hp hp1 hq s hs

/--
[PeriodicGraph.bufferedEdgeWindow_endpoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma bufferedEdgeWindow_endpoint_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {N : ℕ}
  {e : Sym2 V}
  {x : V}
-- given
  (he : e ∈ P.bufferedEdgeWindow N)
  (hx : x ∈ e) :
-- imply
  x ∈ P.orbitBox (P.bufferedRadius N) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.bufferedEdgeWindow_endpoint P he hx

/--
[PeriodicGraph.mem_edgeVertexFinset_of_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma mem_edgeVertexFinset_of_mem_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {F : Finset (Sym2 V)}
  {e : Sym2 V}
  {x : V}
-- given
  (he : e ∈ F)
  (hx : x ∈ e) :
-- imply
  x ∈ PeriodicGraph.edgeVertexFinset F := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicGraph.mem_edgeVertexFinset_of_mem P he hx

/--
[PeriodicPlaneEmbedding.bufferedEdgeWindow_escape](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma bufferedEdgeWindow_escape_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {F : Finset (Sym2 V)}
  {k : ℕ} :
-- imply
  letI : SMul (Multiplicative (Site 2)) (Sym2 V) := ⟨fun g e => Sym2.map (P.shift g.toAdd) e⟩ ∃ g : Multiplicative (Site 2), (↑(F.image (fun e => g⁻¹ • e)) : Set (Sym2 V)) ⊆ (P.bufferedEdgeWindow k)ᶜ := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.bufferedEdgeWindow_escape E F k

/--
[PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_isErgodic](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PeriodicPlanarCanonicalErgodicity.lean)
-/
@[path]
private lemma freeBufferedInfiniteVolume_isErgodic_eq
  [Countable V]
  [DecidableEq V]
  {P : PeriodicGraph V}
  {E : PeriodicPlaneEmbedding P}
  {p q : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 1 ≤ q) :
-- imply
  P.IsErgodic (P.freeBufferedInfiniteVolume hp hp1 (zero_lt_one.trans_le hq) : Measure _) := by
-- proof
  apply StatMech.FK.PeriodicPlanar.PeriodicPlaneEmbedding.freeBufferedInfiniteVolume_isErgodic E hp hp1 hq


-- created on 2026-10-23
