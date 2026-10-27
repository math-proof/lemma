import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FK.PottsInfiniteVolumeTwoPoint
open MeasureTheory Filter Topology StatMech StatMech.FK


/--
[pottsAgreementEvent_isClopen](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma pottsAgreementEvent_isClopen_eq
  {d q : Nat}
  {x y : Site d} :
-- imply
  IsClopen (pottsAgreementEvent d q x y) := by
-- proof
  apply StatMech.FK.pottsAgreementEvent_isClopen d q x y

/--
[freePottsFiniteMeasure_real_pottsAgreementEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma freePottsFiniteMeasure_real_pottsAgreementEvent_eq
  {d n q : Nat}
  [NeZero q]
  {beta J : Real}
  {x y : Site d}
-- given
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  ((freePottsFiniteMeasure d n q beta J : ProbabilityMeasure (PottsConfig d q)) : Measure (PottsConfig d q)).real (pottsAgreementEvent d q x y) = pottsAgreeProb (boxGraph d n) q beta J (⟨x, hx⟩ : boxVerts d n) (⟨y, hy⟩ : boxVerts d n) := by
-- proof
  apply StatMech.FK.freePottsFiniteMeasure_real_pottsAgreementEvent d n q beta J x y hx hy

/--
[freeFiniteMeasure_real_connectedEvent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma freeFiniteMeasure_real_connectedEvent_eq
  {d n : Nat}
  {p q : Real}
  {x y : Site d}
-- given
  (hp : 0 < p)
  (hp1 : p < 1)
  (hq : 0 < q)
  (hx : x ∈ box d n)
  (hy : y ∈ box d n) :
-- imply
  (freeFiniteMeasure d n hp hp1 hq : Measure (ConfigSpace (Sym2 (Site d)))).real {omega | Lattice.Connected d omega x y} = connProb (boxGraph d n) p q (⟨x, hx⟩ : boxVerts d n) (⟨y, hy⟩ : boxVerts d n) := by
-- proof
  apply StatMech.FK.freeFiniteMeasure_real_connectedEvent d n hp hp1 hq x y hx hy

/--
[measure_frontier_connectedEvent_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma measure_frontier_connectedEvent_eq_zero_eq
  {mu : ProbabilityMeasure (ConfigSpace (Sym2 (Site d)))}
  {x y : Site d}
-- given
  (hunique : (mu : Measure _) (atLeastTwoInfinite d) = 0) :
-- imply
  (mu : Measure _) (frontier {omega : ConfigSpace (Sym2 (Site d)) | Lattice.Connected d omega x y}) = 0 := by
-- proof
  apply StatMech.FK.measure_frontier_connectedEvent_eq_zero mu hunique x y

/--
[freePottsJointLimit_agreement_eq_fkTwoPoint](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma freePottsJointLimit_agreement_eq_fkTwoPoint_eq
  {d q : Nat}
  [NeZero q]
  {beta J : Real}
  {Xi : ProbabilityMeasure (PottsJointConfig d q)}
  {mu : ProbabilityMeasure (PottsConfig d q)}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J)
  (phi : Nat -> Nat)
  (hphi : StrictMono phi)
  (hjoint : Tendsto (fun n => freePottsJointFiniteMeasure d (phi n) q beta J (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))])) atTop (nhds Xi))
  (hmu : Xi.map continuous_fst.measurable.aemeasurable = mu)
  (hfk : Xi.map continuous_snd.measurable.aemeasurable = freeInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q)) :
-- imply
  forall x y : Site d, ((mu : Measure (PottsConfig d q)).real (pottsAgreementEvent d q x y)) - 1 / (q : Real) = ((q : Real) - 1) / q * infiniteTwoPointReal (freeInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : Measure (ConfigSpace (Sym2 (Site d)))) x y := by
-- proof
  apply StatMech.FK.freePottsJointLimit_agreement_eq_fkTwoPoint d q hd hq beta J hbeta hJ Xi mu phi hphi hjoint hmu hfk

/--
[freePottsInfiniteVolume_twoPoint_exists](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FK/PottsInfiniteVolumeTwoPoint.lean)
-/
@[path]
private lemma freePottsInfiniteVolume_twoPoint_exists_eq
  {d q : Nat}
  [NeZero q]
  {beta J : Real}
-- given
  (hd : 1 <= d)
  (hq : 2 <= q)
  (hbeta : 0 < beta)
  (hJ : 0 < J) :
-- imply
  ∃ mu : ProbabilityMeasure (PottsConfig d q), forall x y : Site d, ((mu : Measure (PottsConfig d q)).real (pottsAgreementEvent d q x y)) - 1 / (q : Real) = ((q : Real) - 1) / q * infiniteTwoPointReal (freeInfiniteVolume d (by apply sub_pos.mpr rw [Real.exp_lt_one_iff] exact neg_neg_of_pos (mul_pos hbeta hJ)) (by linarith [Real.exp_pos (-(beta * J))]) (by exact_mod_cast (show 0 < q by omega) : (0 : Real) < q) : Measure (ConfigSpace (Sym2 (Site d)))) x y := by
-- proof
  apply StatMech.FK.freePottsInfiniteVolume_twoPoint_exists d q hd hq beta J hbeta hJ


-- created on 2026-10-23
