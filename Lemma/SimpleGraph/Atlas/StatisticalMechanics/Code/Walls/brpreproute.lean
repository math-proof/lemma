import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.Walls.brpreproute
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[brp_trifForestData_of_repRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_trifForestData_of_repRoute_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {a : Fin 3 → Site d}
-- given
  (hxbox : x ∈ box d R)
  (hxtri : bc67_IsGnTrifurcation ω L x)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (habdry : ∀ i, a i ∈ vertexBoundary d R)
  (hxne : ∀ i, a i ≠ x)
  (hainj : Function.Injective a)
  (hsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j))
  (hroute : bcr_RepRoute ω L x a) :
-- imply
  bgc_TrifForestData ω L R := by
-- proof
  apply StatMech.Walls.brp_trifForestData_of_repRoute ω L R a hxbox hxtri hsingle habdry hxne hainj hsep hroute

/--
[brp_tail_survives_boxes](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_tail_survives_boxes_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x arm : Site d}
  {T : Finset (Site d)}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L x) ω) arm).Infinite) :
-- imply
  ∃ b : Site d, (bc67_contractedLattice ω L x).Reachable arm b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, r k ∉ T) ∧ (∀ k, (bc67_contractedLattice ω L x).Adj (r k) (r (k + 1))) ∧ (∀ z : Site d, bc61_boxAround d L z ⊆ T → ∀ k, (bc67_contractedLattice ω L z).Reachable b (r k)) := by
-- proof
  apply StatMech.Walls.brp_tail_survives_boxes ω L x arm hinf T

/--
[brp_repRoute_of_entry](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_repRoute_of_entry_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x : Site d}
  {tip b : Fin 3 → Site d}
-- given
  (hentry : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i))
  (htail : ∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) :
-- imply
  bcr_RepRoute ω L x tip := by
-- proof
  apply StatMech.Walls.brp_repRoute_of_entry ω L x tip b hentry htail

/--
[brp_off_box_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_off_box_coord_eq
  {d : ℕ}
  {L : ℕ}
  {z p : Site 2}
  {i : Fin 2}
-- given
  (h : L < ((p - z) i).natAbs) :
-- imply
  p ∉ bc61_boxAround 2 L z := by
-- proof
  apply StatMech.Walls.brp_off_box_coord i h

/--
[brp_cross_hreach_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_cross_hreach_avoid_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site 2}
  {c : ℤ}
  {j : ℕ}
-- given
  (hoff : ∀ m : ℕ, bc57_pt (c + (m : ℤ)) 0 ∉ bc61_boxAround 2 L z) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross) (bc57_pt c 0) (bc57_pt (c + (j : ℤ)) 0) := by
-- proof
  apply StatMech.Walls.brp_cross_hreach_avoid L z c j hoff

/--
[brp_cross_vreach_up_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_cross_vreach_up_avoid_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site 2}
  {j : ℕ}
-- given
  (hgt : ℤ)
  (hoff : ∀ m : ℕ, bc57_pt 0 (hgt + (m : ℤ)) ∉ bc61_boxAround 2 L z) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross) (bc57_pt 0 hgt) (bc57_pt 0 (hgt + (j : ℤ))) := by
-- proof
  apply StatMech.Walls.brp_cross_vreach_up_avoid L z hgt j hoff

/--
[brp_cross_vreach_down_avoid](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_cross_vreach_down_avoid_eq
  {d : ℕ}
  {L : ℕ}
  {z : Site 2}
  {j : ℕ}
-- given
  (hgt : ℤ)
  (hoff : ∀ m : ℕ, bc57_pt 0 (hgt - (m : ℤ)) ∉ bc61_boxAround 2 L z) :
-- imply
  Connected 2 (removeSites (bc61_boxAround 2 L z) bcr_cross) (bc57_pt 0 hgt) (bc57_pt 0 (hgt - (j : ℤ))) := by
-- proof
  apply StatMech.Walls.brp_cross_vreach_down_avoid L z hgt j hoff

/--
[brp_witArm_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_witArm_zero_eq
  {d : ℕ}
  {R : ℕ} :
-- imply
  brp_witArm R 0 = bc57_pt (R : ℤ) 0 := by
-- proof
  apply StatMech.Walls.brp_witArm_zero R

/--
[brp_witArm_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_witArm_one_eq
  {d : ℕ}
  {R : ℕ} :
-- imply
  brp_witArm R 1 = bc57_pt 0 (R : ℤ) := by
-- proof
  apply StatMech.Walls.brp_witArm_one R

/--
[brp_witArm_two](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_witArm_two_eq
  {d : ℕ}
  {R : ℕ} :
-- imply
  brp_witArm R 2 = bc57_pt 0 (-(R : ℤ)) := by
-- proof
  apply StatMech.Walls.brp_witArm_two R

/--
[brp_cross_repRoute](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_cross_repRoute_eq
  {d : ℕ}
  {L R : ℕ}
-- given
  (hR : L < R) :
-- imply
  bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R) := by
-- proof
  apply StatMech.Walls.brp_cross_repRoute L R hR

/--
[brp_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/brpreproute.lean)
-/
@[path]
private lemma brp_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L R : ℕ) (x : Site d) (a : Fin 3 → Site d), x ∈ box d R → bc67_IsGnTrifurcation ω L x → (∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x) → (∀ i, a i ∈ vertexBoundary d R) → (∀ i, a i ≠ x) → Function.Injective a → (∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (a i) (a j)) → bcr_RepRoute ω L x a → bgc_TrifForestData ω L R) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (x : Site d) (tip b : Fin 3 → Site d), (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable x (b i)) → (∀ i j, i ≠ j → (bc67_contractedLattice ω L (tip j)).Reachable (b i) (tip i)) → bcr_RepRoute ω L x tip) ∧ (∀ (L R : ℕ), L < R → bcr_RepRoute bcr_cross L (bc57_pt 0 0) (brp_witArm R)) := by
-- proof
  apply StatMech.Walls.brp_status


-- created on 2026-10-23
