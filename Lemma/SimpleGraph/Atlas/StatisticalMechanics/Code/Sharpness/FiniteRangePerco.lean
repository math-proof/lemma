import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Sharpness.FiniteRangePerco
open MeasureTheory StatMech StatMech.Sharpness


/--
[frp_finset_subset_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_finset_subset_box_eq
  {d : ℕ}
  {S : Finset (Site d)} :
-- imply
  ∃ N : ℕ, (S : Set (Site d)) ⊆ box d N := by
-- proof
  apply StatMech.Sharpness.frp_finset_subset_box S

/--
[frpEdgeCoupling_mk](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpEdgeCoupling_mk_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {x y : Site d} :
-- imply
  frpEdgeCoupling K s(x, y) = K.coupling (y - x) := by
-- proof
  apply StatMech.Sharpness.frpEdgeCoupling_mk K x y

/--
[frpEdgeParam_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpEdgeParam_le_one_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  (e) :
-- imply
  frpEdgeParam K beta e ≤ 1 := by
-- proof
  apply StatMech.Sharpness.frpEdgeParam_le_one K beta

/--
[frpEdgeCoupling_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpEdgeCoupling_smul_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  frpEdgeCoupling K (g • e) = frpEdgeCoupling K e := by
-- proof
  apply StatMech.Sharpness.frpEdgeCoupling_smul K g e

/--
[frpEdgeParam_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpEdgeParam_smul_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {g : Multiplicative (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  frpEdgeParam K beta (g • e) = frpEdgeParam K beta e := by
-- proof
  apply StatMech.Sharpness.frpEdgeParam_smul K beta g e

/--
[frpMeasure_translationInvariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpMeasure_translationInvariant_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ} :
-- imply
  IsTranslationInvariant (G := Multiplicative (Site d)) (frpMeasure K beta) := by
-- proof
  apply StatMech.Sharpness.frpMeasure_translationInvariant K beta

/--
[frpGraph_adj_displacement](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpGraph_adj_displacement_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {x y : Site d}
-- given
  (hxy : (frpGraph K).Adj x y) :
-- imply
  y - x ∈ box d K.range := by
-- proof
  apply StatMech.Sharpness.frpGraph_adj_displacement K hxy

/--
[mem_frpSteps](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma mem_frpSteps_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {z : Site d} :
-- imply
  z ∈ frpSteps K ↔ 0 < K.coupling z := by
-- proof
  apply StatMech.Sharpness.mem_frpSteps K

/--
[mem_frpBoundaryPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma mem_frpBoundaryPairs_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {x y : Site d} :
-- imply
  (x, y) ∈ frpBoundaryPairs K S ↔ x ∈ S ∧ y ∉ S ∧ (frpGraph K).Adj x y := by
-- proof
  apply StatMech.Sharpness.mem_frpBoundaryPairs K S

/--
[frp_mem_internalEdges](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_mem_internalEdges_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ S)
  (hy : y ∈ S) :
-- imply
  s(x, y) ∈ frpInternalEdges S := by
-- proof
  apply StatMech.Sharpness.frp_mem_internalEdges hx hy

/--
[frp_connWithin_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_connWithin_transfer_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {omega omega' : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {a b : (S : Set (Site d))}
-- given
  (hagree : ∀ e ∈ frpInternalEdges S, omega e = omega' e)
  (h : ConnWithin (frpGraph K) omega (S : Set (Site d)) a b) :
-- imply
  ConnWithin (frpGraph K) omega' (S : Set (Site d)) a b := by
-- proof
  apply StatMech.Sharpness.frp_connWithin_transfer K hagree h

/--
[frp_connEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_connEvent_dependsOn_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {u x : Site d} :
-- imply
  DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u {x}) (frpInternalEdges S : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.frp_connEvent_dependsOn K S u x

/--
[frp_connEvent_set_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_connEvent_set_dependsOn_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {u : Site d}
  {B : Set (Site d)} :
-- imply
  DependsOn (connEvent (frpGraph K) (S : Set (Site d)) u B) (frpInternalEdges S : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.frp_connEvent_set_dependsOn K S u B

/--
[frp_firstExit_inclusion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_firstExit_inclusion_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {A : Set (Site d)}
  {S : Finset (Site d)}
  {B : Set (Site d)}
  {u : Site d}
-- given
  (huS : u ∈ S)
  (hBS : ∀ z ∈ B, z ∉ S) :
-- imply
  connEvent (frpGraph K) A u B ⊆ ⋃ q ∈ frpBoundaryPairs K S, disjointOccurrence (connEvent (frpGraph K) (S : Set (Site d)) u {q.1}) (disjointOccurrence (edgeOpenEvent q.1 q.2) (connEvent (frpGraph K) A q.2 B)) := by
-- proof
  apply StatMech.Sharpness.frp_firstExit_inclusion K A S B u huS hBS

/--
[frp_bk_criterion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_bk_criterion_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {Lam S : Finset (Site d)}
  {u : Site d}
  {B : Set (Site d)}
-- given
  (huS : u ∈ S)
  (hBS : ∀ z ∈ B, z ∉ S) :
-- imply
  (frpMeasure K beta).real (connEvent (frpGraph K) (Lam : Set (Site d)) u B) ≤ ∑ q ∈ frpBoundaryPairs K S, (frpEdgeParam K beta s(q.1, q.2) : ℝ) * (frpMeasure K beta).real (connEvent (frpGraph K) (S : Set (Site d)) u {q.1}) * (frpMeasure K beta).real (connEvent (frpGraph K) (Lam : Set (Site d)) q.2 B) := by
-- proof
  apply StatMech.Sharpness.frp_bk_criterion K beta Lam S u B huS hBS

/--
[frp_adj_mem_box_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_adj_mem_box_add_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {N : ℕ}
  {x y : Site d}
-- given
  (hx : x ∈ box d N)
  (hxy : (frpGraph K).Adj x y) :
-- imply
  y ∈ box d (N + K.range) := by
-- proof
  apply StatMech.Sharpness.frp_adj_mem_box_add K hx hxy

/--
[frp_connWithin_mono_set](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_connWithin_mono_set_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {omega : ConfigSpace (Sym2 (Site d))}
  {S T : Set (Site d)}
  {x y : S}
-- given
  (hST : S ⊆ T)
  (h : ConnWithin (frpGraph K) omega S x y) :
-- imply
  ConnWithin (frpGraph K) omega T ⟨(x : Site d), hST x.2⟩ ⟨(y : Site d), hST y.2⟩ := by
-- proof
  apply StatMech.Sharpness.frp_connWithin_mono_set K omega hST h

/--
[mem_frpCrossingWindow](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma mem_frpCrossingWindow_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {n : ℕ}
  {x : Site d} :
-- imply
  x ∈ frpCrossingWindow K n ↔ x ∈ box d ((n - 1) + K.range) := by
-- proof
  apply StatMech.Sharpness.mem_frpCrossingWindow K n x

/--
[frpCrossingEvent_eq_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossingEvent_eq_finite_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {n : ℕ} :
-- imply
  frpCrossingEvent K n = connEvent (frpGraph K) (frpCrossingWindow K n : Set (Site d)) (0 : Site d) (box d (n - 1))ᶜ := by
-- proof
  apply StatMech.Sharpness.frpCrossingEvent_eq_finite K n

/--
[frpCrossingEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossingEvent_dependsOn_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {n : ℕ} :
-- imply
  DependsOn (frpCrossingEvent K n) (frpInternalEdges (frpCrossingWindow K n) : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.frpCrossingEvent_dependsOn K n

/--
[frp_subset_oneStepClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_subset_oneStepClosure_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)} :
-- imply
  S ⊆ frpOneStepClosure K S := by
-- proof
  apply StatMech.Sharpness.frp_subset_oneStepClosure K S

/--
[frp_boundary_snd_mem_closure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_boundary_snd_mem_closure_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {q : Site d × Site d}
-- given
  (hq : q ∈ frpBoundaryPairs K S) :
-- imply
  q.2 ∈ frpOneStepClosure K S := by
-- proof
  apply StatMech.Sharpness.frp_boundary_snd_mem_closure K S hq

/--
[frp_exitEvent_eq_finite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_exitEvent_eq_finite_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {u : Site d}
-- given
  (huS : u ∈ S) :
-- imply
  connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ = connEvent (frpGraph K) (frpOneStepClosure K S : Set (Site d)) u (S : Set (Site d))ᶜ := by
-- proof
  apply StatMech.Sharpness.frp_exitEvent_eq_finite K S u huS

/--
[frp_exitEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_exitEvent_dependsOn_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {u : Site d}
-- given
  (huS : u ∈ S) :
-- imply
  DependsOn (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ) (frpInternalEdges (frpOneStepClosure K S) : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Sharpness.frp_exitEvent_dependsOn K S u huS

/--
[measurableSet_frp_exitEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma measurableSet_frp_exitEvent_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {S : Finset (Site d)}
  {u : Site d}
-- given
  (huS : u ∈ S) :
-- imply
  MeasurableSet (connEvent (frpGraph K) Set.univ u (S : Set (Site d))ᶜ) := by
-- proof
  apply StatMech.Sharpness.measurableSet_frp_exitEvent K S u huS

/--
[frpGraph_adj_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpGraph_adj_smul_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {g : Multiplicative (Site d)}
  {x y : Site d} :
-- imply
  (frpGraph K).Adj (g • x) (g • y) ↔ (frpGraph K).Adj x y := by
-- proof
  apply StatMech.Sharpness.frpGraph_adj_smul K g x y

/--
[frp_openSub_adj_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_openSub_adj_shift_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  (openSub (frpGraph K) (shift g omega)).Adj (g • x) (g • y) ↔ (openSub (frpGraph K) omega).Adj x y := by
-- proof
  apply StatMech.Sharpness.frp_openSub_adj_shift K g omega x y

/--
[frp_connWithin_univ_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_connWithin_univ_shift_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x y : Site d} :
-- imply
  ConnWithin (frpGraph K) (shift g omega) Set.univ ⟨g • x, Set.mem_univ _⟩ ⟨g • y, Set.mem_univ _⟩ ↔ ConnWithin (frpGraph K) omega Set.univ ⟨x, Set.mem_univ _⟩ ⟨y, Set.mem_univ _⟩ := by
-- proof
  apply StatMech.Sharpness.frp_connWithin_univ_shift K g omega x y

/--
[mem_frpShiftedBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma mem_frpShiftedBox_eq
  {d : ℕ}
  {y z : Site d}
  {n : ℕ} :
-- imply
  z ∈ frpShiftedBox y n ↔ z + y ∈ box d (n - 1) := by
-- proof
  apply StatMech.Sharpness.mem_frpShiftedBox y z n

/--
[frpCrossingEventFrom_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossingEventFrom_zero_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {n : ℕ} :
-- imply
  frpCrossingEventFrom K 0 n = frpCrossingEvent K n := by
-- proof
  apply StatMech.Sharpness.frpCrossingEventFrom_zero K n

/--
[frpCrossingEventFrom_eq_preimage](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossingEventFrom_eq_preimage_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {y : Site d}
  {n : ℕ} :
-- imply
  frpCrossingEventFrom K y n = (shift (Multiplicative.ofAdd (-y)) : ConfigSpace (Sym2 (Site d)) → _) ⁻¹' connEvent (frpGraph K) Set.univ (0 : Site d) (frpShiftedBox y n : Set (Site d))ᶜ := by
-- proof
  apply StatMech.Sharpness.frpCrossingEventFrom_eq_preimage K y n

/--
[frp_crossProbFrom_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_crossProbFrom_le_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {y : Site d}
  {L m n : ℕ}
-- given
  (hy : y ∈ box d L)
  (hmLn : m + L ≤ n)
  (hm : 1 ≤ m) :
-- imply
  (frpMeasure K beta).real (frpCrossingEventFrom K y n) ≤ frpCrossProb K beta m := by
-- proof
  apply StatMech.Sharpness.frp_crossProbFrom_le K beta y hy hmLn hm

/--
[frpCrossProb_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossProb_nonneg_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  0 ≤ frpCrossProb K beta n := by
-- proof
  apply StatMech.Sharpness.frpCrossProb_nonneg K beta n

/--
[frpCrossProb_le_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossProb_le_one_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {n : ℕ} :
-- imply
  frpCrossProb K beta n ≤ 1 := by
-- proof
  apply StatMech.Sharpness.frpCrossProb_le_one K beta n

/--
[frpCrossingEvent_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossingEvent_antitone_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {m n : ℕ}
-- given
  (hmn : m ≤ n) :
-- imply
  frpCrossingEvent K n ⊆ frpCrossingEvent K m := by
-- proof
  apply StatMech.Sharpness.frpCrossingEvent_antitone K hmn

/--
[frpCrossProb_antitone](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpCrossProb_antitone_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ} :
-- imply
  Antitone (frpCrossProb K beta) := by
-- proof
  apply StatMech.Sharpness.frpCrossProb_antitone K beta

/--
[frp_subcritical_oneStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_subcritical_oneStep_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {S : Finset (Site d)}
  {L : ℕ}
  {k : ℕ}
-- given
  (h0S : (0 : Site d) ∈ S)
  (hL : 1 ≤ L)
  (hRL : K.range ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range))
  (hk : 1 ≤ k) :
-- imply
  frpCrossProb K beta ((k + 1) * L) ≤ frpPhi K beta S * frpCrossProb K beta (k * L) := by
-- proof
  apply StatMech.Sharpness.frp_subcritical_oneStep K beta S h0S L hL hRL hSbox k hk

/--
[frpPhi_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpPhi_nonneg_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {S : Finset (Site d)} :
-- imply
  0 ≤ frpPhi K beta S := by
-- proof
  apply StatMech.Sharpness.frpPhi_nonneg K beta S

/--
[frp_subcritical_geometric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_subcritical_geometric_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (h0S : (0 : Site d) ∈ S)
  (hphi : frpPhi K beta S < 1)
  (hL : 1 ≤ L)
  (hRL : K.range ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
-- imply
  ∃ r, 0 < r ∧ r < 1 ∧ ∀ k, frpCrossProb K beta (k * L) ≤ r⁻¹ * r ^ k := by
-- proof
  apply StatMech.Sharpness.frp_subcritical_geometric K beta S h0S hphi L hL hRL hSbox

/--
[frp_subcritical_decay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_subcritical_decay_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {S : Finset (Site d)}
  {L : ℕ}
-- given
  (h0S : (0 : Site d) ∈ S)
  (hphi : frpPhi K beta S < 1)
  (hL : 1 ≤ L)
  (hRL : K.range ≤ L)
  (hSbox : (S : Set (Site d)) ⊆ box d (L - K.range)) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.frp_subcritical_decay K beta S h0S hphi L hL hRL hSbox

/--
[frpEdgeParam_eq_zero_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpEdgeParam_eq_zero_of_nonpos_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {e : Sym2 (Site d)}
-- given
  (hbeta : beta ≤ 0) :
-- imply
  frpEdgeParam K beta e = 0 := by
-- proof
  apply StatMech.Sharpness.frpEdgeParam_eq_zero_of_nonpos K hbeta e

/--
[frpPhi_eq_zero_of_nonpos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpPhi_eq_zero_of_nonpos_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
  {S : Finset (Site d)}
-- given
  (hbeta : beta ≤ 0) :
-- imply
  frpPhi K beta S = 0 := by
-- proof
  apply StatMech.Sharpness.frpPhi_eq_zero_of_nonpos K hbeta S

/--
[frpSubcriticalSet_nonempty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frpSubcriticalSet_nonempty_eq
  {d : ℕ}
  {K : FiniteRangeKernel d} :
-- imply
  (frpSubcriticalSet K).Nonempty := by
-- proof
  apply StatMech.Sharpness.frpSubcriticalSet_nonempty K

/--
[exists_frpPhi_witness_of_lt_tildeBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma exists_frpPhi_witness_of_lt_tildeBetaC_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
-- given
  (hbeta : beta < frpTildeBetaC K) :
-- imply
  ∃ S : Finset (Site d), (0 : Site d) ∈ S ∧ frpPhi K beta S < 1 := by
-- proof
  apply StatMech.Sharpness.exists_frpPhi_witness_of_lt_tildeBetaC K hbeta

/--
[frp_subcritical_decay_of_lt_tildeBetaC](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/FiniteRangePerco.lean)
-/
@[path]
private lemma frp_subcritical_decay_of_lt_tildeBetaC_eq
  {d : ℕ}
  {K : FiniteRangeKernel d}
  {beta : ℝ}
-- given
  (hbeta : beta < frpTildeBetaC K) :
-- imply
  ∃ c > 0, ∃ C > 0, ∀ n, frpCrossProb K beta n ≤ C * Real.exp (-c * n) := by
-- proof
  apply StatMech.Sharpness.frp_subcritical_decay_of_lt_tildeBetaC K hbeta


-- created on 2026-10-23
