import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Percolation.Exploration.Part5
open MeasureTheory Function Set StatMech StatMech.Percolation


/--
[w1_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma w1_sum_eq
  [Fintype E]
  [DecidableEq E]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (∑ b : Bool, w1 p hp b) = 1 := by
-- proof
  apply StatMech.Percolation.w1_sum p hp

/--
[part_norm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma part_norm_eq
  [Fintype E]
  [DecidableEq E]
  {Sₜ : Type*}
  [Fintype Sₜ]
  [DecidableEq Sₜ]
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (∑ x : Sₜ → Bool, ∏ i, w1 p hp (x i)) = 1 := by
-- proof
  apply StatMech.Percolation.part_norm p hp Sₜ

/--
[wsum_mul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma wsum_mul_eq
  [Fintype E]
  [DecidableEq E]
  [DecidablePred P]
  {f g : ConfigSpace E → ℝ}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (P : E → Prop)
  (hf : ∀ ω ω', (∀ e, P e → ω e = ω' e) → f ω = f ω')
  (hg : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → g ω = g ω') :
-- imply
  wsum p hp (fun ω => f ω * g ω) = wsum p hp f * wsum p hp g := by
-- proof
  apply StatMech.Percolation.wsum_mul p hp P f g hf hg

/--
[real_eq_wsum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma real_eq_wsum_eq
  [Fintype E]
  [DecidableEq E]
  {A : Set (ConfigSpace E)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real A = wsum p hp (A.indicator (fun _ => (1 : ℝ))) := by
-- proof
  apply StatMech.Percolation.real_eq_wsum p hp A

/--
[indep_cylinder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma indep_cylinder_eq
  [Fintype E]
  [DecidableEq E]
  [DecidablePred P]
  {A B : Set (ConfigSpace E)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (P : E → Prop)
  (hA : ∀ ω ω', (∀ e, P e → ω e = ω' e) → (ω ∈ A ↔ ω' ∈ A))
  (hB : ∀ ω ω', (∀ e, ¬ P e → ω e = ω' e) → (ω ∈ B ↔ ω' ∈ B)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) = (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Percolation.indep_cylinder p hp P A B hA hB

/--
[indic_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma indic_iff_eq
  [Countable E]
  [DecidableEq E]
  {X : Set (ConfigSpace E)}
  {a b : ConfigSpace E}
-- given
  (h : X.indicator (fun _ => (1:ℝ)) a = X.indicator (fun _ => (1:ℝ)) b) :
-- imply
  (a ∈ X ↔ b ∈ X) := by
-- proof
  apply StatMech.Percolation.indic_iff h

/--
[indep_cylinder_inf](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma indep_cylinder_inf_eq
  [Countable E]
  [DecidableEq E]
  {A B : Set (ConfigSpace E)}
  {T U : Finset E}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hdisj : Disjoint T U)
  (hA : DependsOn (A.indicator (fun _ => (1 : ℝ))) (T : Set E))
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set E)) :
-- imply
  (bernoulliProductMeasure (E := E) p hp).real (A ∩ B) = (bernoulliProductMeasure (E := E) p hp).real A * (bernoulliProductMeasure (E := E) p hp).real B := by
-- proof
  apply StatMech.Percolation.indep_cylinder_inf p hp A B T U hdisj hA hB

/--
[mem_incidentWithin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma mem_incidentWithin_eq
  {d : ℕ}
  {K S : Set (Site d)}
  {x y : Site d}
-- given
  (hx : x ∈ K)
  (hy : y ∈ S) :
-- imply
  s(x, y) ∈ incidentWithin K S := by
-- proof
  apply StatMech.Percolation.mem_incidentWithin hx hy

/--
[agree_KS](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma agree_KS_eq
  {d : ℕ}
  {K S : Set (Site d)}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
  (hx : x ∈ K)
  (hy : y ∈ S) :
-- imply
  ω s(x, y) = ω' s(x, y) := by
-- proof
  apply StatMech.Percolation.agree_KS hagree hx hy

/--
[isOpenEdge_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma isOpenEdge_transfer_eq
  {d : ℕ}
  {K S : Set (Site d)}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {x y : Site d}
-- given
  (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
  (hx : x ∈ K)
  (hy : y ∈ S)
  (h : IsOpenEdge d ω x y) :
-- imply
  IsOpenEdge d ω' x y := by
-- proof
  apply StatMech.Percolation.isOpenEdge_transfer hagree hx hy h

/--
[clusterWithin_closed](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma clusterWithin_closed_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d}
  {x y : Site d}
-- given
  (hx : x ∈ clusterWithin d ω S o)
  (hyS : y ∈ S)
  (hopen : IsOpenEdge d ω x y) :
-- imply
  y ∈ clusterWithin d ω S o := by
-- proof
  apply StatMech.Percolation.clusterWithin_closed hx hyS hopen

/--
[walk_transfer](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma walk_transfer_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d}
  {a b : ↥S}
  {w : (openSubgraphInduce d ω S).Walk a b}
-- given
  (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
  (ha : (a : Site d) ∈ clusterWithin d ω S o) :
-- imply
  (b : Site d) ∈ clusterWithin d ω S o ∧ Nonempty ((openSubgraphInduce d ω' S).Walk a b) := by
-- proof
  apply StatMech.Percolation.walk_transfer hagree w ha

/--
[K_closed_omega'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma K_closed_omega'_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d}
  {x y : Site d}
-- given
  (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
  (hxK : x ∈ clusterWithin d ω S o)
  (hyS : y ∈ S)
  (hopen' : IsOpenEdge d ω' x y) :
-- imply
  y ∈ clusterWithin d ω S o := by
-- proof
  apply StatMech.Percolation.K_closed_omega' hagree hxK hyS hopen'

/--
[walk_trap_omega'](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma walk_trap_omega'_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d}
  {a b : ↥S}
  {w : (openSubgraphInduce d ω' S).Walk a b}
-- given
  (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e)
  (ha : (a : Site d) ∈ clusterWithin d ω S o) :
-- imply
  (b : Site d) ∈ clusterWithin d ω S o := by
-- proof
  apply StatMech.Percolation.walk_trap_omega' hagree w ha

/--
[clusterWithin_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma clusterWithin_congr_eq
  {d : ℕ}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
  {S : Set (Site d)}
  {o : Site d}
-- given
  (hoS : o ∈ S)
  (hagree : ∀ e ∈ incidentWithin (clusterWithin d ω S o) S, ω e = ω' e) :
-- imply
  clusterWithin d ω' S o = clusterWithin d ω S o := by
-- proof
  apply StatMech.Percolation.clusterWithin_congr hoS hagree

/--
[clusterEvent_congr](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma clusterEvent_congr_eq
  {d : ℕ}
  {S : Set (Site d)}
  {o : Site d}
  {K : Set (Site d)}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hoS : o ∈ S)
  (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e)
  (hω : ω ∈ clusterEvent d S o K) :
-- imply
  ω' ∈ clusterEvent d S o K := by
-- proof
  apply StatMech.Percolation.clusterEvent_congr hoS hagree hω

/--
[clusterEvent_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma clusterEvent_iff_eq
  {d : ℕ}
  {S : Set (Site d)}
  {o : Site d}
  {K : Set (Site d)}
  {ω ω' : ConfigSpace (Sym2 (Site d))}
-- given
  (hoS : o ∈ S)
  (hagree : ∀ e ∈ incidentWithin K S, ω e = ω' e) :
-- imply
  ω ∈ clusterEvent d S o K ↔ ω' ∈ clusterEvent d S o K := by
-- proof
  apply StatMech.Percolation.clusterEvent_iff hoS hagree

/--
[mem_incidentWithinFinset](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma mem_incidentWithinFinset_eq
  {d : ℕ}
  {K S : Finset (Site d)}
  {e : Sym2 (Site d)} :
-- imply
  e ∈ incidentWithinFinset K S ↔ ∃ x ∈ K, ∃ y ∈ S, e = s(x, y) := by
-- proof
  apply StatMech.Percolation.mem_incidentWithinFinset

/--
[incidentWithinFinset_coe](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma incidentWithinFinset_coe_eq
  {d : ℕ}
  {K S : Finset (Site d)} :
-- imply
  (incidentWithinFinset K S : Set (Sym2 (Site d))) = incidentWithin (K : Set _) (S : Set _) := by
-- proof
  apply StatMech.Percolation.incidentWithinFinset_coe K S

/--
[clusterEvent_dependsOn](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma clusterEvent_dependsOn_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o : Site d}
  {K : Finset (Site d)}
-- given
  (hoS : o ∈ (S : Set (Site d))) :
-- imply
  DependsOn ((clusterEvent d (S : Set (Site d)) o (K : Set (Site d))).indicator (fun _ => (1 : ℝ))) (incidentWithinFinset K S : Set (Sym2 (Site d))) := by
-- proof
  apply StatMech.Percolation.clusterEvent_dependsOn hoS

/--
[exploration_decomposition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Percolation/Exploration.lean)
-/
@[path]
private lemma exploration_decomposition_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {o : Site d}
  {K : Finset (Site d)}
  {B : Set (ConfigSpace (Sym2 (Site d)))}
  {U : Finset (Sym2 (Site d))}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hoS : o ∈ (S : Set (Site d)))
  (hdisj : Disjoint (incidentWithinFinset K S) U)
  (hB : DependsOn (B.indicator (fun _ => (1 : ℝ))) (U : Set (Sym2 (Site d)))) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) o (K : Set (Site d)) ∩ B) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (clusterEvent d (S : Set (Site d)) o (K : Set (Site d))) * (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real B := by
-- proof
  apply StatMech.Percolation.exploration_decomposition p hp S o hoS K B U hdisj hB


-- created on 2026-10-23
