import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.Universality.IsingFermionicPhysicalHolderBridge.Part2
open StatMech StatMech.Universality


/--
[fkIsingSquareRadialPatchDeepVariation_nonneg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchDeepVariation_nonneg_eq
  {n m : Nat}
  {r : Nat}
  {base : Real}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m) :
-- imply
  0 ≤ fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchDeepVariation_nonneg n m hn hm hm2 r base

/--
[fkIsingSquareRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le_eq
  {n m baseI baseJ R rho : Nat}
  {mesh d H V : Real}
  {r : Nat}
  {base : Real}
  {p p' : IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base ≤ V)
  (hd : 0 ≤ d)
  (hH : 0 ≤ H)
  (hradius : d ≤ mesh * (rho : Real))
  (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
  (hrho : 0 < rho)
  (hp : IsingLeapfrogInteriorMargin R rho p)
  (hp' : IsingLeapfrogInteriorMargin R rho p')
  (hpp' : IsingLeapfrogDiagonalAdjacent p p') :
-- imply
  ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ p - fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ p'‖ ≤ mesh * H := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPhysicalNormalizedWindow_neighbor_norm_sub_le n m baseI baseJ R rho mesh d H V hn hm hm2 hfitI hfitJ hmesh r base hdeep hV hd hH hradius hscale p p' hrho hp hp' hpp'

/--
[fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path_eq
  {n m baseI baseJ R rho steps : Nat}
  {mesh d H V B D : Real}
  {r : Nat}
  {base : Real}
  {gamma : Nat → IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base ≤ V)
  (hd : 0 ≤ d)
  (hH : 0 ≤ H)
  (hradius : d ≤ mesh * (rho : Real))
  (hscale : 1032080 * V ≤ H ^ 2 * d ^ 3)
  (hrho : 0 < rho)
  (hmargin : ∀ k ≤ steps, IsingLeapfrogInteriorMargin R rho (gamma k))
  (hadjacent : ∀ k < steps, IsingLeapfrogDiagonalAdjacent (gamma k) (gamma (k + 1)))
  (hstart : ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma 0)‖ ≤ B)
  (hlength : mesh * (steps : Real) ≤ D) :
-- imply
  ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma steps)‖ ≤ B + D * H := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path n m baseI baseJ R rho steps mesh d H V B D hn hm hm2 hfitI hfitJ hmesh r base hdeep hV hd hH hradius hscale hrho gamma hmargin hadjacent hstart hlength

/--
[fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path_explicit](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Universality/IsingFermionicPhysicalHolderBridge.lean)
-/
@[path]
private lemma fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path_explicit_eq
  {n m baseI baseJ R rho steps : Nat}
  {mesh d V B D : Real}
  {r : Nat}
  {base : Real}
  {gamma : Nat → IsingLeapfrogBox R}
-- given
  (hn : 0 < n)
  (hm : m ≤ n)
  (hm2 : 2 ≤ m)
  (hfitI : baseI + R + 1 < m)
  (hfitJ : baseJ + R + 1 < m)
  (hmesh : 0 < mesh)
  (hdeep : ∀ q : IsingLeapfrogBox R, fkIsingSquareRadialPatchWindowCell m baseI baseJ R hfitI hfitJ q ∈ fkIsingSquareRadialPatchDeepCells n m hm hm2 r)
  (hV : fkIsingSquareRadialPatchDeepVariation n m hn hm hm2 r base ≤ V)
  (hd : 0 < d)
  (hradius : d ≤ mesh * (rho : Real))
  (hrho : 0 < rho)
  (hmargin : ∀ k ≤ steps, IsingLeapfrogInteriorMargin R rho (gamma k))
  (hadjacent : ∀ k < steps, IsingLeapfrogDiagonalAdjacent (gamma k) (gamma (k + 1)))
  (hstart : ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma 0)‖ ≤ B)
  (hlength : mesh * (steps : Real) ≤ D) :
-- imply
  ‖fkIsingSquareRadialPatchPhysicalNormalizedWindow n m baseI baseJ R mesh hn hm hfitI hfitJ (gamma steps)‖ ≤ B + D * Real.sqrt (1032080 * V / d ^ 3) := by
-- proof
  apply StatMech.Universality.fkIsingSquareRadialPatchPhysicalNormalizedWindow_norm_le_of_path_explicit n m baseI baseJ R rho steps mesh d V B D hn hm hm2 hfitI hfitJ hmesh r base hdeep hV hd hradius hrho gamma hmargin hadjacent hstart hlength


-- created on 2026-10-23
