import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Sharpness.PercoSusceptibility.Part5
open MeasureTheory Set Finset Filter StatMech StatMech.Sharpness


/--
[shk_mem_translateFinset_smul](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_mem_translateFinset_smul_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
  {x : Site d} :
-- imply
  g • x ∈ shk_translateFinset g S ↔ x ∈ S := by
-- proof
  apply StatMech.Sharpness.shk_mem_translateFinset_smul g S x

/--
[shk_translateFinset_card](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_translateFinset_card_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)} :
-- imply
  (shk_translateFinset g S).card = S.card := by
-- proof
  apply StatMech.Sharpness.shk_translateFinset_card g S

/--
[shk_connectedWithin_shift_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_connectedWithin_shift_iff_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {omega : ConfigSpace (Sym2 (Site d))}
  {S : Finset (Site d)}
  {x y : S} :
-- imply
  ConnectedWithin d (ConfigSpace.shift g omega) (shk_translateFinset g S : Set (Site d)) ⟨g • (x : Site d), by exact (shk_mem_translateFinset_smul g S x).2 x.2⟩ ⟨g • (y : Site d), by exact (shk_mem_translateFinset_smul g S y).2 y.2⟩ ↔ ConnectedWithin d omega (S : Set (Site d)) x y := by
-- proof
  apply StatMech.Sharpness.shk_connectedWithin_shift_iff g omega S x y

/--
[shk_shift_preimage_connWithinEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_shift_preimage_connWithinEvent_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
  {u x : Site d}
-- given
  (hu : u ∈ S)
  (hx : x ∈ S) :
-- imply
  (ConfigSpace.shift g) ⁻¹' connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x) = connWithinEvent d (S : Set (Site d)) u x := by
-- proof
  apply StatMech.Sharpness.shk_shift_preimage_connWithinEvent g S u x hu hx

/--
[shk_connWithinEvent_prob_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_connWithinEvent_prob_translate_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
  {u x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (hu : u ∈ S)
  (hx : x ∈ S) :
-- imply
  (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • u) (g • x)) = (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (S : Set (Site d)) u x) := by
-- proof
  apply StatMech.Sharpness.shk_connWithinEvent_prob_translate p hp g S u x hu hx

/--
[shk_pairSmul_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_pairSmul_injective_eq
  {d : ℕ}
  {g : Multiplicative (Site d)} :
-- imply
  Function.Injective (shk_pairSmul (d := d) g) := by
-- proof
  apply StatMech.Sharpness.shk_pairSmul_injective g

/--
[shk_boundaryEdges_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_boundaryEdges_translate_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)} :
-- imply
  boundaryEdges d (shk_translateFinset g S) = (boundaryEdges d S).image (shk_pairSmul g) := by
-- proof
  apply StatMech.Sharpness.shk_boundaryEdges_translate g S

/--
[shk_boundaryConnSum_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_boundaryConnSum_translate_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : origin d ∈ S) :
-- imply
  ∑ q ∈ boundaryEdges d (shk_translateFinset g S), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • origin d) q.1) = ∑ q ∈ boundaryEdges d S, connWithinProb d p hp S q.1 := by
-- proof
  apply StatMech.Sharpness.shk_boundaryConnSum_translate p hp g S h0

/--
[shk_phi_translate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_phi_translate_eq
  {d : ℕ}
  {g : Multiplicative (Site d)}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0 : origin d ∈ S) :
-- imply
  (p : ℝ) * ∑ q ∈ boundaryEdges d (shk_translateFinset g S), (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (shk_translateFinset g S : Set (Site d)) (g • origin d) q.1) = phi d p hp S := by
-- proof
  apply StatMech.Sharpness.shk_phi_translate p hp g S h0

/--
[shk_restrictedSusceptibility_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_restrictedSusceptibility_le_eq
  {d : ℕ}
  {S Lam : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0S : origin d ∈ S)
  (h0Lam : origin d ∈ Lam)
  (hphi : phi d p hp S < 1) :
-- imply
  shk_restrictedSusceptibility p hp Lam (origin d) ≤ (S.card : ℝ) / (1 - phi d p hp S) := by
-- proof
  apply StatMech.Sharpness.shk_restrictedSusceptibility_le p hp S Lam h0S h0Lam hphi

/--
[shk_connWithinProb_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_connWithinProb_mono_eq
  {d : ℕ}
  {p q : ℝ≥0}
  {S : Finset (Site d)}
  {x : Site d}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (hpq : p ≤ q) :
-- imply
  connWithinProb d p hp S x ≤ connWithinProb d q hq S x := by
-- proof
  apply StatMech.Sharpness.shk_connWithinProb_mono hp hq hpq S x

/--
[shk_phi_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_phi_mono_eq
  {d : ℕ}
  {p q : ℝ≥0}
  {S : Finset (Site d)}
-- given
  (hp : p ≤ 1)
  (hq : q ≤ 1)
  (hpq : p ≤ q) :
-- imply
  phi d p hp S ≤ phi d q hq S := by
-- proof
  apply StatMech.Sharpness.shk_phi_mono hp hq hpq S

/--
[bondParam_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma bondParam_mono_eq
  {d : ℕ} :
-- imply
  Monotone bondParam := by
-- proof
  apply StatMech.Sharpness.bondParam_mono

/--
[exists_phiBeta_witness_of_lt_tildeBetaCPerco](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma exists_phiBeta_witness_of_lt_tildeBetaCPerco_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : beta < tildeBetaCPerco d) :
-- imply
  ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d beta S < 1 := by
-- proof
  apply StatMech.Sharpness.exists_phiBeta_witness_of_lt_tildeBetaCPerco hbeta

/--
[shk_withinBoxEvent_mono](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_withinBoxEvent_mono_eq
  {d : ℕ}
  {x : Site d} :
-- imply
  Monotone (fun n : ℕ => connWithinEvent d (box d n) (origin d) x) := by
-- proof
  apply StatMech.Sharpness.shk_withinBoxEvent_mono x

/--
[shk_connected_iff_mem_iUnion_withinBox](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_connected_iff_mem_iUnion_withinBox_eq
  {d : ℕ}
  {omega : ConfigSpace (Sym2 (Site d))}
  {x : Site d} :
-- imply
  Connected d omega (origin d) x ↔ omega ∈ ⋃ n : ℕ, connWithinEvent d (box d n) (origin d) x := by
-- proof
  apply StatMech.Sharpness.shk_connected_iff_mem_iUnion_withinBox omega x

/--
[shk_connWithinBox_tendsto_twoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_connWithinBox_tendsto_twoPoint_eq
  {d : ℕ}
  {x : Site d}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1) :
-- imply
  Tendsto (fun n => (bernoulliProductMeasure (E := Sym2 (Site d)) p hp).real (connWithinEvent d (box d n) (origin d) x)) atTop (nhds (shk_twoPointProb p hp x)) := by
-- proof
  apply StatMech.Sharpness.shk_connWithinBox_tendsto_twoPoint p hp x

/--
[shk_twoPoint_partialSum_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_twoPoint_partialSum_le_eq
  {d : ℕ}
  {S : Finset (Site d)}
  {T : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0S : origin d ∈ S)
  (hphi : phi d p hp S < 1) :
-- imply
  ∑ x ∈ T, shk_twoPointProb p hp x ≤ (S.card : ℝ) / (1 - phi d p hp S) := by
-- proof
  apply StatMech.Sharpness.shk_twoPoint_partialSum_le p hp S h0S hphi T

/--
[shk_twoPoint_summable_of_phi_lt_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma shk_twoPoint_summable_of_phi_lt_one_eq
  {d : ℕ}
  {S : Finset (Site d)}
-- given
  (p : ℝ≥0)
  (hp : p ≤ 1)
  (h0S : origin d ∈ S)
  (hphi : phi d p hp S < 1) :
-- imply
  Summable (shk_twoPointProb (d := d) p hp) := by
-- proof
  apply StatMech.Sharpness.shk_twoPoint_summable_of_phi_lt_one p hp S h0S hphi

/--
[finite_susceptibility_of_lt_tildeBetaCPerco](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Sharpness/PercoSusceptibility.lean)
-/
@[path]
private lemma finite_susceptibility_of_lt_tildeBetaCPerco_eq
  {d : ℕ}
  {beta : ℝ}
-- given
  (hbeta : beta < tildeBetaCPerco d) :
-- imply
  ∃ S : Finset (Site d), origin d ∈ S ∧ phiBeta d beta S < 1 ∧ Summable (shk_twoPointProb (d := d) (bondParam beta) (bondParam_le_one beta)) ∧ ∀ Lam : Finset (Site d), origin d ∈ Lam → shk_restrictedSusceptibility (bondParam beta) (bondParam_le_one beta) Lam (origin d) ≤ (S.card : ℝ) / (1 - phiBeta d beta S) := by
-- proof
  apply StatMech.Sharpness.finite_susceptibility_of_lt_tildeBetaCPerco hbeta


-- created on 2026-10-23
