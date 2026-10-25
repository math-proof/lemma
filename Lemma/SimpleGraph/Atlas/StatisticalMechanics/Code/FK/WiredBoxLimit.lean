import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FK.WiredBoxLimit.Part2
open MeasureTheory Filter Topology SimpleGraph StatMech StatMech.FK


/--
[extendEdge_crossExt](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma extendEdge_crossExt_eq
  {d : ℕ}
  {d n : ℕ}
  {ω : ConfigSpace (Sym2 (boxVerts d n))} :
-- imply
  extendEdge d (n+1) (crossExt d n ω) = extendEdge d n ω := by
-- proof
  apply StatMech.FK.extendEdge_crossExt d n ω

/--
[boxRestrict_extendEdge_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma boxRestrict_extendEdge_succ_eq
  {d : ℕ}
  {d n : ℕ}
  {ρ : ConfigSpace (Sym2 (boxVerts d (n+1)))} :
-- imply
  boxRestrict d n (extendEdge d (n+1) ρ) = innerRestrict d n ρ := by
-- proof
  apply StatMech.FK.boxRestrict_extendEdge_succ d n ρ

/--
[isIncreasing_innerBdryFinEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma isIncreasing_innerBdryFinEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  IsIncreasing (innerBdryFinEvent d n) := by
-- proof
  apply StatMech.FK.isIncreasing_innerBdryFinEvent d n

/--
[extendEdge_succ_preimage_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma extendEdge_succ_preimage_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  extendEdge d (n+1) ⁻¹' (boxBdryConnEvent d n) = innerBdryFinEvent d n := by
-- proof
  apply StatMech.FK.extendEdge_succ_preimage_boxBdryConnEvent d n

/--
[crossExt_preimage_innerBdryFinEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma crossExt_preimage_innerBdryFinEvent_eq
  {d : ℕ}
  {d n : ℕ} :
-- imply
  crossExt d n ⁻¹' (innerBdryFinEvent d n) = {ω : ConfigSpace (Sym2 (boxVerts d n)) | ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)} := by
-- proof
  apply StatMech.FK.crossExt_preimage_innerBdryFinEvent d n

/--
[wiredFiniteMeasure_succ_real_boxBdryConnEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma wiredFiniteMeasure_succ_real_boxBdryConnEvent_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d (n+1) hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) = ∑ ρ : ConfigSpace (Sym2 (boxVerts d (n+1))), (innerBdryFinEvent d n).indicator (fun _ => (1:ℝ)) ρ * wiredFkProb (boxGraph d (n+1)) (boxBoundary d (n+1)) p 2 ρ := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_succ_real_boxBdryConnEvent d n hp hp1

/--
[wiredFiniteMeasure_real_boxBdryConnEvent_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma wiredFiniteMeasure_real_boxBdryConnEvent_sum_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), {ω : ConfigSpace (Sym2 (boxVerts d n)) | ConnToBdry (boxGraph d n) (boxBoundary d n) ω (IsingFK.boxOrigin d n)}.indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p 2 ω := by
-- proof
  apply StatMech.FK.wiredFiniteMeasure_real_boxBdryConnEvent_sum d n hp hp1

/--
[condBcProb_add_sum_eq_smallerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma condBcProb_add_sum_eq_smallerBox_eq
  {d : ℕ}
  {d n : ℕ}
  {p q : ℝ}
  {D : SimpleGraph (boxVerts d (n+1))}
  [DecidableRel D.Adj]
  {B : Set (ConfigSpace (Sym2 (boxVerts d (n+1))))}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq0 : 0 < q)
  (hD : IsAnnulusWiring d n D) :
-- imply
  (∑ ρ, B.indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (innerBdry d n) ⊔ D) p q (innerEdgeFinset d n) (fun _ => false) ρ) = ∑ ω : ConfigSpace (Sym2 (boxVerts d n)), (crossExt d n ⁻¹' B).indicator (fun _ => (1:ℝ)) ω * wiredFkProb (boxGraph d n) (boxBoundary d n) p q ω := by
-- proof
  apply StatMech.FK.condBcProb_add_sum_eq_smallerBox d n hp hp1 hq0 hD B

/--
[condWiredSucc_le_smallerBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/WiredBoxLimit.lean)
-/
@[path]
private lemma condWiredSucc_le_smallerBox_eq
  {d : ℕ}
  {d n : ℕ}
  {p : ℝ}
-- given
  (hp : 0 < p)
  (hp1 : p < 1) :
-- imply
  (∑ ρ, (innerBdryFinEvent d n).indicator (fun _ => (1:ℝ)) ρ * condBcProb (boxGraph d (n+1)) (StatMech.Lattice.boundaryCliqueGraph (boxBoundary d (n+1))) p 2 (innerEdgeFinset d n) (fun _ => false) ρ) ≤ (wiredFiniteMeasure d n hp hp1 (by norm_num : (0:ℝ) < 2) : Measure (ConfigSpace (Sym2 (Site d)))).real (boxBdryConnEvent d n) := by
-- proof
  apply StatMech.FK.condWiredSucc_le_smallerBox d n hp hp1


-- created on 2026-10-23
