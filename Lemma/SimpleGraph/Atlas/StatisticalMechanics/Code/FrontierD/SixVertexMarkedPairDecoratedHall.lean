import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexMarkedPairDecoratedHall.Part3
open Finset Matrix Polynomial StatMech StatMech.FrontierD


/--
[sixVertexMarkedPairMultiplicity_eq_natCast](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexMarkedPairMultiplicity_eq_natCast_eq
  {T : EvenTorus}
  {omega eta : SixVertexArrows T}
  {k : Nat}
-- given
  (homega : omega.IceRule)
  (heta : eta.IceRule) :
-- imply
  sixVertexMarkedPairMultiplicity omega eta k = (sixVertexMarkedPairMultiplicityNat omega eta k : Real) := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedPairMultiplicity_eq_natCast omega eta homega heta k

/--
[card_sixVertexMarkedDecoratedPair_eq_pairMass](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma card_sixVertexMarkedDecoratedPair_eq_pairMass_eq
  {T : EvenTorus}
  {left right : Fin (T.width + 1)}
  {k : Nat} :
-- imply
  (Fintype.card (SixVertexMarkedDecoratedPair T left right k) : Real) = sixVertexMarkedSectorPairMass T left right k := by
-- proof
  apply StatMech.FrontierD.card_sixVertexMarkedDecoratedPair_eq_pairMass T left right k

/--
[sixVertexMarkedDecoratedPairHall_of_bidegree](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_of_bidegree_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {degree : Nat}
-- given
  (related : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop)
  (hdegree : 0 < degree)
  (hsource : forall source, degree <= (Finset.univ.filter (related source)).card)
  (htarget : forall target, (Finset.univ.filter fun source => related source target).card <= degree) :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k related := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_of_bidegree related degree hdegree hsource htarget

/--
[sixVertexMarkedDecoratedPairHall_iff_exists_injective](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexMarkedDecoratedPairHall_iff_exists_injective_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
-- given
  (related : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop) :
-- imply
  SixVertexMarkedDecoratedPairHall T lower middle upper k related <-> exists matching : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k, Function.Injective matching /\ forall source, related source (matching source) := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedDecoratedPairHall_iff_exists_injective T lower middle upper k related

/--
[sixVertexMarkedSectorPairMass_le_of_decoratedHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexMarkedSectorPairMass_le_of_decoratedHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {related : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop}
-- given
  (hall : SixVertexMarkedDecoratedPairHall T lower middle upper k related) :
-- imply
  sixVertexMarkedSectorPairMass T lower upper k <= sixVertexMarkedSectorPairMass T middle middle k := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedSectorPairMass_le_of_decoratedHall hall

/--
[coeff_shiftedSectorTrace_mul_le_sq_of_decoratedHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma coeff_shiftedSectorTrace_mul_le_sq_of_decoratedHall_eq
  {T : EvenTorus}
  {lower middle upper : Fin (T.width + 1)}
  {k : Nat}
  {related : SixVertexMarkedDecoratedPair T lower upper k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop}
-- given
  (hall : SixVertexMarkedDecoratedPairHall T lower middle upper k related) :
-- imply
  (sixVertexShiftedSectorTracePolynomial T.width T.height lower.val * sixVertexShiftedSectorTracePolynomial T.width T.height upper.val).coeff k <= (sixVertexShiftedSectorTracePolynomial T.width T.height middle.val ^ 2).coeff k := by
-- proof
  apply StatMech.FrontierD.coeff_shiftedSectorTrace_mul_le_sq_of_decoratedHall hall

/--
[sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hall : forall k : Nat, exists related : SixVertexMarkedDecoratedPair T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop, SixVertexMarkedDecoratedPairHall T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩ k related) :
-- imply
  SixVertexMarkedTraceCoefficientwiseLogConcave T.width T.height middle.val := by
-- proof
  apply StatMech.FrontierD.sixVertexMarkedTraceCoefficientwiseLogConcave_of_decoratedHall T middle hmiddle_pos hmiddle_lt hall

/--
[sixVertexSectorTrace_logConcave_of_decoratedHall](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexMarkedPairDecoratedHall.lean)
-/
@[path]
private lemma sixVertexSectorTrace_logConcave_of_decoratedHall_eq
  {T : EvenTorus}
  {middle : Fin (T.width + 1)}
  {c : Real}
-- given
  (hmiddle_pos : 0 < middle.val)
  (hmiddle_lt : middle.val < T.width)
  (hc : 2 <= c)
  (hall : forall k : Nat, exists related : SixVertexMarkedDecoratedPair T ⟨middle.val - 1, by omega⟩ ⟨middle.val + 1, by omega⟩ k -> SixVertexMarkedDecoratedPair T middle middle k -> Prop, SixVertexMarkedDecoratedPairHall T ⟨middle.val - 1, by omega⟩ middle ⟨middle.val + 1, by omega⟩ k related) :
-- imply
  Matrix.trace (sixVertexSectorTransfer T.width (middle.val - 1) c ^ T.height) * Matrix.trace (sixVertexSectorTransfer T.width (middle.val + 1) c ^ T.height) <= Matrix.trace (sixVertexSectorTransfer T.width middle.val c ^ T.height) ^ 2 := by
-- proof
  apply StatMech.FrontierD.sixVertexSectorTrace_logConcave_of_decoratedHall T middle hmiddle_pos hmiddle_lt hc hall


-- created on 2026-10-23
