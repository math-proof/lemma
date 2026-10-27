import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Walls.jc8touchingfaceband
open SimpleGraph Function Set StatMech StatMech.Walls


/--
[jc8tf_earFootprint_row](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_earFootprint_row_eq
  {r x : Site 2}
-- given
  (hx : x ∈ jc3_earFootprint r) :
-- imply
  r 1 - 1 ≤ x 1 ∧ x 1 ≤ r 1 + 1 := by
-- proof
  apply StatMech.Walls.jc8tf_earFootprint_row r x hx

/--
[jc8tf_dartFace_row_near_probes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_dartFace_row_near_probes_eq
  {d : Dart} :
-- imply
  (dartFace d 1 - jc_headTravel d 1).natAbs ≤ 2 ∧ (dartFace d 1 - jc_tailTravel d 1).natAbs ≤ 2 := by
-- proof
  apply StatMech.Walls.jc8tf_dartFace_row_near_probes d

/--
[jc8tf_probingDart_dartFace_row_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_probingDart_dartFace_row_band_eq
  {r : Site 2}
  {d : Dart}
-- given
  (hprobe : jc5_ProbesEarFootprint r d) :
-- imply
  r 1 - 3 ≤ dartFace d 1 ∧ dartFace d 1 ≤ r 1 + 3 := by
-- proof
  apply StatMech.Walls.jc8tf_probingDart_dartFace_row_band r d hprobe

/--
[jc8tf_touchingDart_of_touchingStep](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_touchingDart_of_touchingStep_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (he : IsBoundaryDart K e)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  jc5_ProbesEarFootprint r ((dartNext K)^[j] e) := by
-- proof
  apply StatMech.Walls.jc8tf_touchingDart_of_touchingStep K e he r j htouch

/--
[jc8tf_touchingFace_row_band](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_touchingFace_row_band_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 ∧ (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 + 3 := by
-- proof
  apply StatMech.Walls.jc8tf_touchingFace_row_band K hK e he r j hj htouch

/--
[jc8tf_touchingFace_within_three](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_touchingFace_within_three_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  ((olb_orbitLoop K hK e he).getVert j 1 - r 1).natAbs ≤ 3 := by
-- proof
  apply StatMech.Walls.jc8tf_touchingFace_within_three K hK e he r j hj htouch

/--
[jc8tf_touchingFace_lower](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_touchingFace_lower_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  r 1 - 3 ≤ (olb_orbitLoop K hK e he).getVert j 1 := by
-- proof
  apply StatMech.Walls.jc8tf_touchingFace_lower K hK e he r j hj htouch

/--
[jc8tf_touchingFace_upper](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_touchingFace_upper_eq
  {K : Set (Site 2)}
  {e : Dart}
  {r : Site 2}
  {j : ℕ}
-- given
  (hK : K.Finite)
  (he : IsBoundaryDart K e)
  (hj : j ≤ (olb_orbitLoop K hK e he).length)
  (htouch : ¬ jc4_FootprintFree K ⟨e, he⟩ r j) :
-- imply
  (olb_orbitLoop K hK e he).getVert j 1 ≤ r 1 + 3 := by
-- proof
  apply StatMech.Walls.jc8tf_touchingFace_upper K hK e he r j hj htouch

/--
[jc8tf_dartFace_row_near_probes_self](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_dartFace_row_near_probes_self_eq :
-- imply
  (dartFace (mkDart (![0, 0] : Site 2) (![1, 0] : Site 2) (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 - jc_headTravel (mkDart (![0, 0] : Site 2) (![1, 0] : Site 2) (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1).natAbs ≤ 2 := by
-- proof
  apply StatMech.Walls.jc8tf_dartFace_row_near_probes_self

/--
[jc8tf_band_nonvacuous](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/jc8touchingfaceband.lean)
-/
@[path]
private lemma jc8tf_band_nonvacuous_eq :
-- imply
  (![0, 0] : Site 2) 1 - 3 ≤ dartFace (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2) (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 ∧ dartFace (mkDart (![0, 1] : Site 2) (![1, 0] : Site 2) (by unfold unitWt; rw [Fin.sum_univ_two]; simp)) 1 ≤ (![0, 0] : Site 2) 1 + 3 := by
-- proof
  apply StatMech.Walls.jc8tf_band_nonvacuous


-- created on 2026-10-23
