import Mathlib
import sympy.Basic
import Theorem.StatisticalMechanics.Code.FrontierA.GrahamCanonicalEdgeDegreeHall.Part6
open Finset StatMech StatMech.FrontierA StatMech.GrahamGHS StatMech.GrahamGHS.FourColor


/--
[card_le_bipartiteNeighbors_of_edgeDegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma card_le_bipartiteNeighbors_of_edgeDegree_eq
  [Fintype A]
  [Fintype B]
  [DecidableRel r]
  {S : Finset A}
-- given
  (r : A -> B -> Prop)
  (hne : ∀ a ∈ S, (Finset.univ.filter (r a)).Nonempty)
  (hdeg : ∀ a ∈ S, ∀ b, r a b -> (Finset.univ.filter fun x => r x b).card <= (Finset.univ.filter (r a)).card) :
-- imply
  S.card <= (Finset.univ.filter fun b => ∃ a ∈ S, r a b).card := by
-- proof
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_edgeDegree r S hne hdeg

/--
[tightBipartiteNeighborhood_collisionSurplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma tightBipartiteNeighborhood_collisionSurplus_eq
  [Fintype A]
  [Fintype B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
-- given
  (r : A -> B -> Prop)
  (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
  (htight : N.card + 1 = S.card) :
-- imply
  (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card = (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card + 1 := by
-- proof
  apply StatMech.FrontierA.tightBipartiteNeighborhood_collisionSurplus r S N hN htight

/--
[bipartiteNeighborhood_collisionSurplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma bipartiteNeighborhood_collisionSurplus_eq
  [Fintype A]
  [Fintype B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
-- given
  (r : A -> B -> Prop)
  (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
-- imply
  (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card = (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card + ((S.card : ℤ) - N.card) := by
-- proof
  apply StatMech.FrontierA.bipartiteNeighborhood_collisionSurplus r S N hN

/--
[card_le_bipartiteNeighbors_of_collisionSurplus](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma card_le_bipartiteNeighbors_of_collisionSurplus_eq
  [Fintype A]
  [Fintype B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
-- given
  (r : A -> B -> Prop)
  (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
  (hsurplus : (∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤ (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) :
-- imply
  S.card ≤ N.card := by
-- proof
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionSurplus r S N hN hsurplus

/--
[bipartiteNeighborhood_collisionSurplus_iff_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma bipartiteNeighborhood_collisionSurplus_iff_card_le_eq
  [Fintype A]
  [Fintype B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
-- given
  (r : A -> B -> Prop)
  (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b) :
-- imply
  ((∑ b ∈ N, ((S.filter fun a => r a b).card : ℤ)) - N.card ≤ (∑ a ∈ S, ((Finset.univ.filter (r a)).card : ℤ)) - S.card) ↔ S.card ≤ N.card := by
-- proof
  apply StatMech.FrontierA.bipartiteNeighborhood_collisionSurplus_iff_card_le r S N hN

/--
[bipartiteLeftSurplusToken_eq_of_source_target_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma bipartiteLeftSurplusToken_eq_of_source_target_eq_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq B]
  [DecidableRel r]
  {S : Finset A}
  {x y : bipartiteLeftSurplusToken r S base}
-- given
  (r : A -> B -> Prop)
  (base : ↑S -> B)
  (hsource : x.1 = y.1)
  (htarget : x.2.1 = y.2.1) :
-- imply
  x = y := by
-- proof
  apply StatMech.FrontierA.bipartiteLeftSurplusToken_eq_of_source_target_eq r S base hsource htarget

/--
[cycleCollisionAndSurplusTokenEmbeddings](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma cycleCollisionAndSurplusTokenEmbeddings_eq
  [Fintype A]
  [Fintype B]
  [Fintype C]
  [DecidableEq A]
  [DecidableEq B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
  {σ : Equiv.Perm C}
-- given
  (r : A -> B -> Prop)
  (leftBase : ↑S -> B)
  (rightBase : ↑N -> A)
  (source : C -> ↑S)
  (target : C -> ↑N)
  (hσ : ∀ x, σ x ≠ x)
  (htarget : Function.Injective target)
  (hsourceNext : ∀ x, source x ≠ source (σ x))
  (hcurrent : ∀ x, r (source x).1 (target x).1)
  (hnext : ∀ x, r (source x).1 (target (σ x)).1)
  (hexceptional : ∀ x, (source x).1 ≠ rightBase (target x)) :
-- imply
  Nonempty (C ↪ bipartiteRightCollisionToken r S N rightBase) ∧ Nonempty (C ↪ bipartiteLeftSurplusToken r S leftBase) := by
-- proof
  apply StatMech.FrontierA.cycleCollisionAndSurplusTokenEmbeddings r S N leftBase rightBase σ source target hσ htarget hsourceNext hcurrent hnext hexceptional

/--
[card_le_bipartiteNeighbors_of_collisionTokenEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma card_le_bipartiteNeighbors_of_collisionTokenEmbedding_eq
  [Fintype A]
  [Fintype B]
  [DecidableEq A]
  [DecidableEq B]
  [DecidableRel r]
  {S : Finset A}
  {N : Finset B}
-- given
  (r : A -> B -> Prop)
  (hN : N = Finset.univ.filter fun b => ∃ a ∈ S, r a b)
  (hemb : BipartiteCollisionTokenEmbedding r S N) :
-- imply
  S.card ≤ N.card := by
-- proof
  apply StatMech.FrontierA.card_le_bipartiteNeighbors_of_collisionTokenEmbedding r S N hN hemb

/--
[canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hemb : CanonicalMaskRightEdgePreimageEmbedding ends m j k l zero p) :
-- imply
  CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightEdgeDegreeDominance_of_preimageEmbedding ends m j k l zero p hemb

/--
[canonicalMaskRightPreimageReference_works](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma canonicalMaskRightPreimageReference_works_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (d : {d : leftMaskFiber ends m j k l zero p // q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
-- imply
  CanonicalTransferWorks ends m k zero (canonicalMaskRightPreimageReference ends m j k l zero p q d).1.1 d.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightPreimageReference_works ends m j k l zero p q d

/--
[canonicalMaskRightPreimageReference_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma canonicalMaskRightPreimageReference_eq_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
  {q : rightMaskFiber ends m j k l zero p}
-- given
  (ends : I -> Sym2 W)
  (d : {d : leftMaskFiber ends m j k l zero p // q ∈ canonicalMaskRightImages ends m j k l zero p d}) :
-- imply
  q.1.1 = balancedSwap m (canonicalMiddleTransfer ends m (canonicalMaskRightPreimageReference ends m j k l zero p q d).1.1 k zero) (canonicalOuterTransfer ends m (canonicalMaskRightPreimageReference ends m j k l zero p q d).1.1 k zero) d.1.1.1 := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightPreimageReference_eq ends m j k l zero p q d

/--
[canonicalMaskRightEdgeDegreeDominance_of_selectedOppositeClosure](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/GrahamCanonicalEdgeDegreeHall.lean)
-/
@[path]
private lemma canonicalMaskRightEdgeDegreeDominance_of_selectedOppositeClosure_eq
  [Fintype I]
  [DecidableEq I]
  {m : Finset I}
  {j k l zero : W}
  {p : Finset I × Finset I}
-- given
  (ends : I -> Sym2 W)
  (hloop : ∀ i ∈ m, ¬ (ends i).IsDiag)
  (hjk : j ≠ k)
  (hkl : k ≠ l)
  (hclose : CanonicalMaskRightSelectedOppositeClosure ends m j k l zero p) :
-- imply
  CanonicalMaskRightEdgeDegreeDominance ends m j k l zero p := by
-- proof
  apply StatMech.GrahamGHS.FourColor.canonicalMaskRightEdgeDegreeDominance_of_selectedOppositeClosure ends m j k l zero hloop hjk hkl p hclose


-- created on 2026-10-23
