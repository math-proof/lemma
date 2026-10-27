import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.SurfaceKacWardTwist.Part7
open Finset SimpleGraph StatMech StatMech.FrontierA


/--
[surfaceSpinLinearParity_local_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceSpinLinearParity_local_add_eq
  {a b x y x' y' : Fin 2} :
-- imply
  a * (x + x') + b * (y + y') = (a * x + b * y) + (a * x' + b * y') := by
-- proof
  apply StatMech.FrontierA.surfaceSpinLinearParity_local_add a b x y x' y'

/--
[surfaceSpinLinearParity_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceSpinLinearParity_add_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h k : SurfaceHomology g) :
-- imply
  surfaceSpinLinearParity lambda (h + k) = surfaceSpinLinearParity lambda h + surfaceSpinLinearParity lambda k := by
-- proof
  apply StatMech.FrontierA.surfaceSpinLinearParity_add lambda h k

/--
[surfaceQuadraticParity_eq_base_add_linear](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceQuadraticParity_eq_base_add_linear_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h : SurfaceHomology g) :
-- imply
  surfaceQuadraticParity lambda h = surfaceBaseQuadraticParity h + surfaceSpinLinearParity lambda h := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_eq_base_add_linear lambda h

/--
[surfaceQuadraticParity_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceQuadraticParity_zero_eq
  {g : Nat}
-- given
  (h : SurfaceHomology g) :
-- imply
  surfaceQuadraticParity (0 : SurfaceSpinStructure g) h = surfaceBaseQuadraticParity h := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticParity_zero h

/--
[surfaceHomologyCharacter_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceHomologyCharacter_zero_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g} :
-- imply
  surfaceHomologyCharacter lambda 0 = 1 := by
-- proof
  apply StatMech.FrontierA.surfaceHomologyCharacter_zero lambda

/--
[surfaceHomologyCharacter_add](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceHomologyCharacter_add_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h k : SurfaceHomology g) :
-- imply
  surfaceHomologyCharacter lambda (h + k) = surfaceHomologyCharacter lambda h * surfaceHomologyCharacter lambda k := by
-- proof
  apply StatMech.FrontierA.surfaceHomologyCharacter_add lambda h k

/--
[surfaceHomologyCharacter_finset_sum](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceHomologyCharacter_finset_sum_eq
  {g : Nat}
  [DecidableEq ι]
  {lambda : SurfaceSpinStructure g}
  {S : Finset ι}
  {f : ι → SurfaceHomology g} :
-- imply
  surfaceHomologyCharacter lambda (∑ i ∈ S, f i) = ∏ i ∈ S, surfaceHomologyCharacter lambda (f i) := by
-- proof
  apply StatMech.FrontierA.surfaceHomologyCharacter_finset_sum lambda S f

/--
[prod_surfaceTwistedEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma prod_surfaceTwistedEdgeWeight_eq
  {g : Nat}
  [DecidableEq V]
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex}
  {F : Finset (Sym2 V)} :
-- imply
  (∏ edge ∈ F, surfaceTwistedEdgeWeight edgeClass lambda weight edge) = surfaceHomologyCharacter lambda (surfaceSubgraphHomology edgeClass F) * ∏ edge ∈ F, weight edge := by
-- proof
  apply StatMech.FrontierA.prod_surfaceTwistedEdgeWeight edgeClass lambda weight F

/--
[surfaceParitySign_quadratic_twist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceParitySign_quadratic_twist_eq
  {g : Nat}
  {lambda : SurfaceSpinStructure g}
-- given
  (h : SurfaceHomology g) :
-- imply
  (surfaceParitySign (surfaceQuadraticParity lambda h) : Complex) = (surfaceParitySign (surfaceBaseQuadraticParity h) : Complex) * surfaceHomologyCharacter lambda h := by
-- proof
  apply StatMech.FrontierA.surfaceParitySign_quadratic_twist lambda h

/--
[surfaceQuadraticEvenPolynomial_twist](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceQuadraticEvenPolynomial_twist_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex} :
-- imply
  surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) (surfaceTwistedEdgeWeight edgeClass lambda weight) = surfaceQuadraticEvenPolynomial G edgeClass lambda weight := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticEvenPolynomial_twist G edgeClass lambda weight

/--
[surfaceTwistedKacWardMatrix_apply](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceTwistedKacWardMatrix_apply_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex}
  {d e : G.Dart} :
-- imply
  surfaceTwistedKacWardMatrix G phase edgeClass lambda weight d e = if d.snd = e.fst ∧ d.edge ≠ e.edge then surfaceHomologyCharacter lambda (edgeClass d.edge) * weight d.edge * phase d e else 0 := by
-- proof
  apply StatMech.FrontierA.surfaceTwistedKacWardMatrix_apply G phase edgeClass lambda weight d e

/--
[surface_twisted_kacWard_det_square_of_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surface_twisted_kacWard_det_square_of_base_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {weight : Sym2 V → Complex}
-- given
  (hbase : ∀ w : Sym2 V → Complex, (1 - kwGraphTransition G w phase).det = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) w ^ 2) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda weight).det = surfaceQuadraticEvenPolynomial G edgeClass lambda weight ^ 2 := by
-- proof
  apply StatMech.FrontierA.surface_twisted_kacWard_det_square_of_base G phase edgeClass hbase lambda weight

/--
[surfaceTwistedSectorRoot_graphSectorWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceTwistedSectorRoot_graphSectorWeight_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {edgeClass : Sym2 V → SurfaceHomology g}
  {weight : Sym2 V → Real}
  {lambda : SurfaceSpinStructure g} :
-- imply
  surfaceTwistedSectorRoot (surfaceGraphSectorWeight G edgeClass weight) lambda = ∑ F ∈ G.edgeFinset.powerset.filter IsEvenSubgraph, surfaceParitySign (surfaceQuadraticParity lambda (surfaceSubgraphHomology edgeClass F)) * ∏ edge ∈ F, weight edge := by
-- proof
  apply StatMech.FrontierA.surfaceTwistedSectorRoot_graphSectorWeight G edgeClass weight lambda

/--
[surfaceQuadraticEvenPolynomial_real_eq_sectorRoot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surfaceQuadraticEvenPolynomial_real_eq_sectorRoot_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {edgeClass : Sym2 V → SurfaceHomology g}
  {weight : Sym2 V → Real}
  {lambda : SurfaceSpinStructure g} :
-- imply
  surfaceQuadraticEvenPolynomial G edgeClass lambda (fun edge => (weight edge : Complex)) = (surfaceTwistedSectorRoot (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
-- proof
  apply StatMech.FrontierA.surfaceQuadraticEvenPolynomial_real_eq_sectorRoot G edgeClass weight lambda

/--
[surface_twisted_kacWard_det_eq_sectorSquare_of_base](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/SurfaceKacWardTwist.lean)
-/
@[path]
private lemma surface_twisted_kacWard_det_eq_sectorSquare_of_base_eq
  {g : Nat}
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {phase : G.Dart → G.Dart → Complex}
  {edgeClass : Sym2 V → SurfaceHomology g}
  {lambda : SurfaceSpinStructure g}
  {weight : Sym2 V → Real}
-- given
  (hbase : ∀ w : Sym2 V → Complex, (1 - kwGraphTransition G w phase).det = surfaceQuadraticEvenPolynomial G edgeClass (0 : SurfaceSpinStructure g) w ^ 2) :
-- imply
  (1 - surfaceTwistedKacWardMatrix G phase edgeClass lambda (fun edge => (weight edge : Complex))).det = (surfaceTwistedSectorSquare (surfaceGraphSectorWeight G edgeClass weight) lambda : Complex) := by
-- proof
  apply StatMech.FrontierA.surface_twisted_kacWard_det_eq_sectorSquare_of_base G phase edgeClass hbase lambda weight


-- created on 2026-10-23
