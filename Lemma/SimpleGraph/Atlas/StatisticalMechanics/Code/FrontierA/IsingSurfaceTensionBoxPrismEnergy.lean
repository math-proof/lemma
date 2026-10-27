import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.IsingSurfaceTensionBoxPrismEnergy.Part5
open StatMech StatMech.FrontierA


/--
[spin_glue_rectangularPrismConfigEquiv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_rectangularPrismConfigEquiv_eq
  {eta : ConfigSpace (Site 3)}
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
  {v : RectangularPrismSite (2 * n + 1) (2 * n + 1) n} :
-- imply
  spin (glue eta (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) (rectangularPrismSiteEquivSctBoxDobrushin n v).1 = spin sigma v := by
-- proof
  apply StatMech.FrontierA.spin_glue_rectangularPrismConfigEquiv eta n sigma v

/--
[oddPrism_xZero_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_xZero_exterior_not_mem_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1 0 (-1) ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_xZero_exterior_not_mem n y z

/--
[oddPrism_xLast_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_xLast_exterior_not_mem_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨Fin.last (2 * n), y, z⟩).1 0 1 ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_xLast_exterior_not_mem n y z

/--
[oddPrism_yZero_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_yZero_exterior_not_mem_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1 1 (-1) ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_yZero_exterior_not_mem n x z

/--
[oddPrism_yLast_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_yLast_exterior_not_mem_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, Fin.last (2 * n), z⟩).1 1 1 ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_yLast_exterior_not_mem n x z

/--
[oddPrism_zZero_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_zZero_exterior_not_mem_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1 2 1 ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_zZero_exterior_not_mem n x y

/--
[oddPrism_zLast_exterior_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrism_zLast_exterior_not_mem_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)} :
-- imply
  coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1) ∉ box 3 n := by
-- proof
  apply StatMech.FrontierA.oddPrism_zLast_exterior_not_mem n x y

/--
[spin_glue_plus_of_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_of_not_mem_eq
  {n : Nat}
  {x : Site 3}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
  (hx : x ∉ box 3 n) :
-- imply
  spin (glue (plusField 3) tau) x = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_of_not_mem n tau hx

/--
[spin_glue_plus_xZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_xZero_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1 0 (-1)) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_xZero n tau y z

/--
[spin_glue_plus_xLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_xLast_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨Fin.last (2 * n), y, z⟩).1 0 1) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_xLast n tau y z

/--
[spin_glue_plus_yZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_yZero_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1 1 (-1)) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_yZero n tau x z

/--
[spin_glue_plus_yLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_yLast_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, Fin.last (2 * n), z⟩).1 1 1) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_yLast n tau x z

/--
[spin_glue_plus_zZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_zZero_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1 2 1) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_zZero n tau x y

/--
[spin_glue_plus_zLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_plus_zLast_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (plusField 3) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) = 1 := by
-- proof
  apply StatMech.FrontierA.spin_glue_plus_zLast n tau x y

/--
[bond_glue_plus_oddPrismTouchIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma bond_glue_plus_oddPrismTouchIndex_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
  {q : OddPrismTouchIndex n} :
-- imply
  bond (glue (plusField 3) (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) (oddPrismTouchIndexBond n q) = oddPrismPlusInteractionTerm n sigma q := by
-- proof
  apply StatMech.FrontierA.bond_glue_plus_oddPrismTouchIndex n sigma q

/--
[sum_oddPrismPlusInteractionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma sum_oddPrismPlusInteractionTerm_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ q, oddPrismPlusInteractionTerm n sigma q) = rectangularPrismInternalInteraction sigma + oddRectangularPrismFaceInteraction n sigma := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismPlusInteractionTerm n sigma

/--
[fvEnergy_plus_eq_rectangularPrismPlusEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma fvEnergy_plus_eq_rectangularPrismPlusEnergy_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0 (rectangularPrismConfigEquivSctBoxDobrushin n sigma) = rectangularPrismPlusEnergy 1 sigma := by
-- proof
  apply StatMech.FrontierA.fvEnergy_plus_eq_rectangularPrismPlusEnergy n sigma

/--
[rectangularPrismPlusEnergy_eq_mul_fvEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma rectangularPrismPlusEnergy_eq_mul_fvEnergy_eq
  {J : Real}
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  rectangularPrismPlusEnergy J sigma = J * fvEnergy (plusField 3) n (bondFinsetTouch 3 n) 0 (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
-- proof
  apply StatMech.FrontierA.rectangularPrismPlusEnergy_eq_mul_fvEnergy J n sigma

/--
[rectangularPrismPlusPartition_eq_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma rectangularPrismPlusPartition_eq_fvZ_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  rectangularPrismPlusPartition J beta (2 * n + 1) (2 * n + 1) n = fvZ (plusField 3) n (bondFinsetTouch 3 n) (beta * J) 0 := by
-- proof
  apply StatMech.FrontierA.rectangularPrismPlusPartition_eq_fvZ J beta n

/--
[oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  oddRectangularPrismMeanNegEnergy J beta n = J * fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) (beta * J) 0 := by
-- proof
  apply StatMech.FrontierA.oddRectangularPrismMeanNegEnergy_eq_fvMeanNegEnergy J beta n

/--
[hasDerivAt_log_rectangularPrismPlusPartition](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma hasDerivAt_log_rectangularPrismPlusPartition_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  HasDerivAt (fun b => Real.log (rectangularPrismPlusPartition J b (2 * n + 1) (2 * n + 1) n)) (oddRectangularPrismMeanNegEnergy J beta n) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_log_rectangularPrismPlusPartition J beta n

/--
[spin_glue_interface_of_not_mem_coord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_of_not_mem_coord_eq
  {n : Nat}
  {x : Site 3}
  {z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
  (hx : x ∉ box 3 n)
  (hx2 : x 2 = (n : Int) - z.val) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) x = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_of_not_mem_coord n tau hx z hx2

/--
[spin_glue_interface_of_not_mem_coord_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_of_not_mem_coord_at_eq
  {n : Nat}
  {i : Fin 3}
  {x : Site 3}
  {z : Fin (2 * n + 1)}
-- given
  (hi : i.val = 2)
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool)
  (hx : x ∉ box 3 n)
  (hx2 : x 2 = (n : Int) - z.val) :
-- imply
  spin (glue (interfaceField i) tau) x = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_of_not_mem_coord_at n i hi tau hx z hx2

/--
[spin_glue_interface_xZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_xZero_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨0, y, z⟩).1 0 (-1)) = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_xZero n tau y z

/--
[spin_glue_interface_xLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_xLast_eq
  {n : Nat}
  {y z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨Fin.last (2 * n), y, z⟩).1 0 1) = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_xLast n tau y z

/--
[spin_glue_interface_yZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_yZero_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, 0, z⟩).1 1 (-1)) = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_yZero n tau x z

/--
[spin_glue_interface_yLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_yLast_eq
  {n : Nat}
  {x z : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, Fin.last (2 * n), z⟩).1 1 1) = oddRectangularPrismDobrushinSign n z := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_yLast n tau x z

/--
[spin_glue_interface_zZero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_zZero_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1 2 1) = oddRectangularPrismDobrushinSign n 0 := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_zZero n tau x y

/--
[spin_glue_interface_zLast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_zLast_eq
  {n : Nat}
  {x y : Fin (2 * n + 1)}
-- given
  (hn : 0 < n)
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) = oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_zLast n hn tau x y

/--
[spin_glue_interface_zZero_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_zZero_at_eq
  {n : Nat}
  {i : Fin 3}
  {x y : Fin (2 * n + 1)}
-- given
  (hi : i.val = 2)
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField i) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, 0⟩).1 2 1) = oddRectangularPrismDobrushinSign n 0 := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_zZero_at n i hi tau x y

/--
[spin_glue_interface_zLast_at](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma spin_glue_interface_zLast_at_eq
  {n : Nat}
  {i : Fin 3}
  {x y : Fin (2 * n + 1)}
-- given
  (hn : 0 < n)
  (hi : i.val = 2)
  (tau : {x : Site 3 // x ∈ box 3 n} -> Bool) :
-- imply
  spin (glue (interfaceField i) tau) (coordShift (rectangularPrismSiteEquivSctBoxDobrushin n ⟨x, y, Fin.last (2 * n)⟩).1 2 (-1)) = oddRectangularPrismDobrushinSign n (Fin.last (2 * n)) := by
-- proof
  apply StatMech.FrontierA.spin_glue_interface_zLast_at n hn i hi tau x y

/--
[bond_glue_interface_oddPrismTouchIndex](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma bond_glue_interface_oddPrismTouchIndex_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
  {q : OddPrismTouchIndex n}
-- given
  (hn : 0 < n) :
-- imply
  bond (glue (interfaceField (⟨2, by omega⟩ : Fin 3)) (rectangularPrismConfigEquivSctBoxDobrushin n sigma)) (oddPrismTouchIndexBond n q) = oddPrismDobrushinInteractionTerm n sigma q := by
-- proof
  apply StatMech.FrontierA.bond_glue_interface_oddPrismTouchIndex n hn sigma q

/--
[sum_oddPrismDobrushinInteractionTerm](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma sum_oddPrismDobrushinInteractionTerm_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ q, oddPrismDobrushinInteractionTerm n sigma q) = rectangularPrismInternalInteraction sigma + oddRectangularPrismDobrushinFaceInteraction n sigma := by
-- proof
  apply StatMech.FrontierA.sum_oddPrismDobrushinInteractionTerm n sigma

/--
[fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy_eq
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) 0 (rectangularPrismConfigEquivSctBoxDobrushin n sigma) = oddRectangularPrismDobrushinEnergy 1 n sigma := by
-- proof
  apply StatMech.FrontierA.fvEnergy_interface_eq_oddRectangularPrismDobrushinEnergy n hn sigma

/--
[oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy_eq
  {J : Real}
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n}
-- given
  (hn : 0 < n) :
-- imply
  oddRectangularPrismDobrushinEnergy J n sigma = J * fvEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) 0 (rectangularPrismConfigEquivSctBoxDobrushin n sigma) := by
-- proof
  apply StatMech.FrontierA.oddRectangularPrismDobrushinEnergy_eq_mul_fvEnergy J n hn sigma

/--
[sum_rectangularPrismDobrushinCoupling_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma sum_rectangularPrismDobrushinCoupling_eq_eq
  {J beta : Real}
  {n : Nat}
  {sigma : RectangularPrismConfig (2 * n + 1) (2 * n + 1) n} :
-- imply
  (∑ q : RectangularPrismInteraction (2 * n + 1) (2 * n + 1) n, rectangularPrismDobrushinCoupling J beta q * rectangularPrismInteractionMonomial q sigma) = -beta * oddRectangularPrismDobrushinEnergy J n sigma := by
-- proof
  apply StatMech.FrontierA.sum_rectangularPrismDobrushinCoupling_eq J beta n sigma

/--
[rectangularPrismDobrushinPartition_eq_fvZ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma rectangularPrismDobrushinPartition_eq_fvZ_eq
  {J beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  rectangularPrismDobrushinPartition J beta (2 * n + 1) (2 * n + 1) n = fvZ (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) (beta * J) 0 := by
-- proof
  apply StatMech.FrontierA.rectangularPrismDobrushinPartition_eq_fvZ J beta n hn

/--
[oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy_eq
  {J beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  StatMech.Ising.rectangularDobrushinFreeEnergy J beta (2 * n + 1) (2 * n + 1) n = finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) n (beta * J) := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_eq_finiteInterfaceFreeEnergy J beta n hn

/--
[standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity_eq
  {beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  standardCubicInterfaceDensity beta n = rectangularPrismInterfaceDensity beta n := by
-- proof
  apply StatMech.FrontierA.standardCubicInterfaceDensity_eq_rectangularPrismInterfaceDensity beta n hn

/--
[hasStandardPrismSurfaceComparison](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma hasStandardPrismSurfaceComparison_eq
  {beta : Real} :
-- imply
  HasStandardPrismSurfaceComparison beta := by
-- proof
  apply StatMech.FrontierA.hasStandardPrismSurfaceComparison beta

/--
[hasDerivAt_oddPrismDobrushinFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismDobrushinFreeEnergy_eq
  {J beta : Real}
  {n : Nat}
-- given
  (hn : 0 < n) :
-- imply
  HasDerivAt (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b (2 * n + 1) (2 * n + 1) n) (J * (fvMeanNegEnergy (plusField 3) n (bondFinsetTouch 3 n) (beta * J) 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) n (bondFinsetTouch 3 n) (beta * J) 0)) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismDobrushinFreeEnergy J beta n hn

/--
[oddPrismDobrushinFreeEnergy_succ_eq_finiteInterfaceFreeEnergy](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma oddPrismDobrushinFreeEnergy_succ_eq_finiteInterfaceFreeEnergy_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  StatMech.Ising.rectangularDobrushinFreeEnergy J beta (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1) = finiteInterfaceFreeEnergy (⟨2, by omega⟩ : Fin 3) (n + 1) (beta * J) := by
-- proof
  apply StatMech.FrontierA.oddPrismDobrushinFreeEnergy_succ_eq_finiteInterfaceFreeEnergy J beta n

/--
[hasDerivAt_oddPrismDobrushinFreeEnergy_succ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingSurfaceTensionBoxPrismEnergy.lean)
-/
@[path]
private lemma hasDerivAt_oddPrismDobrushinFreeEnergy_succ_eq
  {J beta : Real}
  {n : Nat} :
-- imply
  HasDerivAt (fun b => StatMech.Ising.rectangularDobrushinFreeEnergy J b (2 * (n + 1) + 1) (2 * (n + 1) + 1) (n + 1)) (J * (fvMeanNegEnergy (plusField 3) (n + 1) (bondFinsetTouch 3 (n + 1)) (beta * J) 0 - fvMeanNegEnergy (interfaceField (⟨2, by omega⟩ : Fin 3)) (n + 1) (bondFinsetTouch 3 (n + 1)) (beta * J) 0)) beta := by
-- proof
  apply StatMech.FrontierA.hasDerivAt_oddPrismDobrushinFreeEnergy_succ J beta n


-- created on 2026-10-23
