import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.Walls.bararmray
open Set SimpleGraph Finset MeasureTheory Filter Topology StatMech StatMech.Lattice StatMech.ConfigSpace StatMech.Walls


/--
[bar_armRay_of_infiniteComponent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_armRay_of_infiniteComponent_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a : Site d}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧ (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1))) ∧ (∀ k, (bc67_contractedLattice ω L y).Reachable a (r k)) := by
-- proof
  apply StatMech.Walls.bar_armRay_of_infiniteComponent ω L y a hinf

/--
[bar_boxAvoiding_armRay](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_boxAvoiding_armRay_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y a : Site d}
  {T : Finset (Site d)}
-- given
  (hinf : (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite) :
-- imply
  ∃ b : Site d, (bc67_contractedLattice ω L y).Reachable a b ∧ ∃ r : ℕ → Site d, r 0 = b ∧ Function.Injective r ∧ (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1))) ∧ (∀ k, r k ∉ T) := by
-- proof
  apply StatMech.Walls.bar_boxAvoiding_armRay ω L y a hinf T

/--
[bar_ray_exits_box](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_ray_exits_box_eq
  {d : ℕ}
  {r : ℕ → Site d}
  {R : ℕ}
-- given
  (hinj : Function.Injective r) :
-- imply
  ∃ k, r k ∉ box d R := by
-- proof
  apply StatMech.Walls.bar_ray_exits_box r hinj R

/--
[bar_ray_crosses_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_ray_crosses_boundary_eq
  {d : ℕ}
  {r : ℕ → Site d}
  {R : ℕ}
-- given
  (hinj : Function.Injective r)
  (hadj : ∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1)))
  (hR : 1 ≤ R)
  (h0 : r 0 ∈ box d R) :
-- imply
  ∃ k, r k ∈ vertexBoundary d R := by
-- proof
  apply StatMech.Walls.bar_ray_crosses_boundary r hinj hadj R hR h0

/--
[bar_armSep_of_rays](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_armSep_of_rays_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {y : Site d}
  {a b p q : Site d}
-- given
  (hpa : (bc67_contractedLattice ω L y).Reachable a p)
  (hqb : (bc67_contractedLattice ω L y).Reachable b q)
  (hab : ¬ (bc67_contractedLattice ω L y).Reachable a b) :
-- imply
  ¬ (bc67_contractedLattice ω L y).Reachable p q := by
-- proof
  apply StatMech.Walls.bar_armSep_of_rays ω L y hpa hqb hab

/--
[bar_center_not_adj](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_center_not_adj_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x z : Site d} :
-- imply
  ¬ (bc67_contractedLattice ω L x).Adj x z := by
-- proof
  apply StatMech.Walls.bar_center_not_adj ω L x z

/--
[bar_center_reach_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_center_reach_eq_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L : ℕ}
  {x z : Site d}
-- given
  (h : (bc67_contractedLattice ω L x).Reachable x z) :
-- imply
  z = x := by
-- proof
  apply StatMech.Walls.bar_center_reach_eq ω L h

/--
[bar_trifForestData_of_arms_route](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_trifForestData_of_arms_route_eq
  {d : ℕ}
  {ω : ConfigSpace (Sym2 (Site d))}
  {L R : ℕ}
  {x : Site d}
  {arm : Fin 3 → Site d}
-- given
  (hR : 1 ≤ R)
  (hxbox : x ∈ box d R)
  (hxtri : bc67_IsGnTrifurcation ω L x)
  (hsingle : ∀ y, y ∈ box d R → bc67_IsGnTrifurcation ω L y → y = x)
  (harmbox : ∀ i, arm i ∈ box d R)
  (harmne : ∀ i, arm i ≠ x)
  (harminf : ∀ i, (cluster d (removeSites (bc61_boxAround d L x) ω) (arm i)).Infinite)
  (harmsep : ∀ i j, i ≠ j → ¬ (bc67_contractedLattice ω L x).Reachable (arm i) (arm j))
  (hroute : ∀ a : Fin 3 → Site d, (∀ i, (bc67_contractedLattice ω L x).Reachable (arm i) (a i)) → (∀ i, a i ∈ vertexBoundary d R) → ∀ i j, i ≠ j → (bc67_contractedLattice ω L (a j)).Reachable x (a i)) :
-- imply
  bgc_TrifForestData ω L R := by
-- proof
  apply StatMech.Walls.bar_trifForestData_of_arms_route ω L R hR arm hxbox hxtri hsingle harmbox harmne harminf harmsep hroute

/--
[bar_bk_uniqueness_of_trifData](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_bk_uniqueness_of_trifData_eq
  {d : ℕ}
-- given
  (p : ℝ≥0)
  (hp1 : p ≤ 1)
  (hp0 : 0 < p)
  (hdata : ∀ (ω : ConfigSpace (Sym2 (Site 2))) (L R : ℕ), bgc_TrifForestData ω L R) :
-- imply
  bernoulliProductMeasure (E := Sym2 (Site 2)) p hp1 (atLeastTwoInfinite 2) = 0 := by
-- proof
  apply StatMech.Walls.bar_bk_uniqueness_of_trifData p hp1 hp0 hdata

/--
[bar_status](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/Walls/bararmray.lean)
-/
@[path]
private lemma bar_status_eq
  {d : ℕ} :
-- imply
  (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a : Site d), (cluster d (removeSites (bc61_boxAround d L y) ω) a).Infinite → ∃ r : ℕ → Site d, r 0 = a ∧ Function.Injective r ∧ (∀ k, (bc67_contractedLattice ω L y).Adj (r k) (r (k + 1)))) ∧ (∀ (ω : ConfigSpace (Sym2 (Site d))) (L : ℕ) (y a b p q : Site d), (bc67_contractedLattice ω L y).Reachable a p → (bc67_contractedLattice ω L y).Reachable b q → ¬ (bc67_contractedLattice ω L y).Reachable a b → ¬ (bc67_contractedLattice ω L y).Reachable p q) ∧ (∀ (r : ℕ → Site d), Function.Injective r → (∀ k, (hypercubicLattice d).Adj (r k) (r (k + 1))) → ∀ R : ℕ, 1 ≤ R → r 0 ∈ box d R → ∃ k, r k ∈ vertexBoundary d R) := by
-- proof
  apply StatMech.Walls.bar_status


-- created on 2026-10-23
