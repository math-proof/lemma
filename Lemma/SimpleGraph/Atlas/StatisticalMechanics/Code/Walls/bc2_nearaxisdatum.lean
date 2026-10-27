import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.bc2_nearaxisdatum.Part2
open MeasureTheory Set StatMech.Lattice StatMech.ConfigSpace StatMech StatMech.Walls


/--
[bc2_nearAxis_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_nearAxis_mem_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc2_NearAxis ω x j) :
-- imply
  hrHD_rayPt j 1 ∈ cluster d ω x := by
-- proof
  apply StatMech.Walls.bc2_nearAxis_mem ω h

/--
[bc2_nearAxis_connected](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_nearAxis_connected_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc2_NearAxis ω x j) :
-- imply
  Connected d (removeSite 0 ω) (hrHD_rayPt j 1) x := by
-- proof
  apply StatMech.Walls.bc2_nearAxis_connected ω h

/--
[bc2_nearAxis_infinite](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_nearAxis_infinite_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc2_NearAxis ω x j) :
-- imply
  (cluster d (removeSite 0 ω) x).Infinite := by
-- proof
  apply StatMech.Walls.bc2_nearAxis_infinite ω h

/--
[bc2_clusterReachesRay_of_nearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_clusterReachesRay_of_nearAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x : Site d}
  {j : Fin d}
-- given
  (h : bc2_NearAxis ω x j) :
-- imply
  lma_ClusterReachesRay ω x j := by
-- proof
  apply StatMech.Walls.bc2_clusterReachesRay_of_nearAxis ω x j h

/--
[bc2_attachData_of_three_nearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_attachData_of_three_nearAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : bc2_NearAxis ω x₁ j₁)
  (h1 : bc2_NearAxis ω x₂ j₂)
  (h2 : bc2_NearAxis ω x₃ j₃) :
-- imply
  tex_AttachData ω x₁ x₂ x₃ := by
-- proof
  apply StatMech.Walls.bc2_attachData_of_three_nearAxis ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[bc2_threeClustersReachOrigin_of_three_nearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_threeClustersReachOrigin_of_three_nearAxis_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {x₁ x₂ x₃ : Site d}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω x₁ ≠ cluster d ω x₂)
  (hcd13 : cluster d ω x₁ ≠ cluster d ω x₃)
  (hcd23 : cluster d ω x₂ ≠ cluster d ω x₃)
  (h0 : bc2_NearAxis ω x₁ j₁)
  (h1 : bc2_NearAxis ω x₂ j₂)
  (h2 : bc2_NearAxis ω x₃ j₃) :
-- imply
  ∃ W : Finset (Sym2 (Site d)), mco_ThreeClustersReachOrigin (forceOpenFinset W ω) := by
-- proof
  apply StatMech.Walls.bc2_threeClustersReachOrigin_of_three_nearAxis ω x₁ x₂ x₃ j₁ j₂ j₃ hcd12 hcd13 hcd23 h0 h1 h2

/--
[bc2_boxReachesRay_of_boxNearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_boxReachesRay_of_boxNearAxis_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc2_BoxNearAxis d n) :
-- imply
  lma_BoxClusterReachesRay d n := by
-- proof
  apply StatMech.Walls.bc2_boxReachesRay_of_boxNearAxis h

/--
[bc2_boxAttachData_of_boxNearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_boxAttachData_of_boxNearAxis_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc2_BoxNearAxis d n) :
-- imply
  tex_BoxAttachData d n := by
-- proof
  apply StatMech.Walls.bc2_boxAttachData_of_boxNearAxis h

/--
[bc2_disjointRouting_of_boxNearAxis](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_disjointRouting_of_boxNearAxis_eq
  {d : ℕ}
  {n : ℕ}
-- given
  (h : bc2_BoxNearAxis d n) :
-- imply
  hrHD_DisjointRouting d n := by
-- proof
  apply StatMech.Walls.bc2_disjointRouting_of_boxNearAxis h

/--
[bc2_nearAxis_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_nearAxis_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  bc2_NearAxis ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Walls.bc2_nearAxis_neighbour ω j hinf

/--
[bc2_clusterReachesRay_neighbour](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_clusterReachesRay_neighbour_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j : Fin d}
-- given
  (hinf : (cluster d (removeSite 0 ω) (hrHD_rayPt j 1)).Infinite) :
-- imply
  lma_ClusterReachesRay ω (hrHD_rayPt j 1) j := by
-- proof
  apply StatMech.Walls.bc2_clusterReachesRay_neighbour ω j hinf

/--
[bc2_attachData_of_neighbour_witnesses](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_attachData_of_neighbour_witnesses_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {j₁ j₂ j₃ : Fin d}
-- given
  (hcd12 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1))
  (hcd13 : cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hcd23 : cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1))
  (hi1 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite)
  (hi2 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite)
  (hi3 : (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite) :
-- imply
  tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1) := by
-- proof
  apply StatMech.Walls.bc2_attachData_of_neighbour_witnesses ω hcd12 hcd13 hcd23 hi1 hi2 hi3

/--
[bc2_nad_core](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bc2_nearaxisdatum.lean)
-/
@[path]
private lemma bc2_nad_core_eq
  {d : ℕ}
  {n : ℕ} :
-- imply
  (bc2_BoxNearAxis d n → tex_BoxAttachData d n ∧ hrHD_DisjointRouting d n) ∧ (∀ {j₁ j₂ j₃ : Fin d} (ω : ConfigSpace (Sym2 (Site d))), cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₂ 1) → cluster d ω (hrHD_rayPt j₁ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) → cluster d ω (hrHD_rayPt j₂ 1) ≠ cluster d ω (hrHD_rayPt j₃ 1) → (cluster d (removeSite 0 ω) (hrHD_rayPt j₁ 1)).Infinite → (cluster d (removeSite 0 ω) (hrHD_rayPt j₂ 1)).Infinite → (cluster d (removeSite 0 ω) (hrHD_rayPt j₃ 1)).Infinite → tex_AttachData ω (hrHD_rayPt j₁ 1) (hrHD_rayPt j₂ 1) (hrHD_rayPt j₃ 1)) := by
-- proof
  apply StatMech.Walls.bc2_nad_core n


-- created on 2026-10-23
