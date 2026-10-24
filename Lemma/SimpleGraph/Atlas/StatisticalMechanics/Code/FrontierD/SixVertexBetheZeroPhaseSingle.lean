import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierD.SixVertexBetheZeroPhaseSingle
open Finset Filter Topology StatMech StatMech.FrontierD


/--
[sixVertexBetheL_phase_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheL_phase_ne_zero_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c) :
-- imply
  sixVertexBetheL c (sixVertexBethePhase y) ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheL_phase_ne_zero hc y

/--
[sixVertexTheta_zero_exp_neg_eq_neg_M_div_L](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexTheta_zero_exp_neg_eq_neg_M_div_L_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c)
  (hy : sixVertexBethePhase y ≠ 1) :
-- imply
  Complex.exp (-Complex.I * sixVertexTheta c 0 y) = -sixVertexBetheM c (sixVertexBethePhase y) / sixVertexBetheL c (sixVertexBethePhase y) := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_zero_exp_neg_eq_neg_M_div_L hc hy

/--
[sixVertexBetheZeroDerivative_algebra](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroDerivative_algebra_eq
  {c : Real}
  {y : Real}
-- given
  (hc : 2 < c)
  (hy : sixVertexBethePhase y ≠ 1) :
-- imply
  sixVertexBetheM c (sixVertexBethePhase y) * ((2 : Complex) - (c : Complex) ^ 2) - 1 - sixVertexBetheM c (sixVertexBethePhase y) / sixVertexBetheL c (sixVertexBethePhase y) = sixVertexBetheM c (sixVertexBethePhase y) * (c : Complex) ^ 2 * sixVertexThetaLeftDerivAtZero c y := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroDerivative_algebra hc hy

/--
[sixVertexBetheZeroAdjacentPairFactor_eq_deriv](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroAdjacentPairFactor_eq_deriv_eq
  {c : Real}
  {y eps : Real}
-- given
  (hc : 2 < c)
  (hy : sixVertexBethePhase y ≠ 1)
  (heps : sixVertexBethePhase eps ≠ 1) :
-- imply
  (sixVertexBetheM c (sixVertexBethePhase y) * sixVertexBetheL c (sixVertexBethePhase eps) - 1) - Complex.exp (-Complex.I * sixVertexTheta c 0 y) * (sixVertexBetheM c (sixVertexBethePhase eps) * sixVertexBetheL c (sixVertexBethePhase y) - 1) = (c : Complex) ^ 2 * sixVertexBetheM c (sixVertexBethePhase y) * sixVertexThetaLeftDerivAtZero c y := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroAdjacentPairFactor_eq_deriv hc hy heps

/--
[sixVertexBethePerturbedWordTerm_adjacent_zero_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordTerm_adjacent_zero_pair_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
  {sigma : Equiv.Perm (Fin (n + 1))}
-- given
  (hc : 2 < c)
  (hell : p ell = 0)
  (heps : sixVertexBethePhase eps ≠ 1)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hzero : sigma i.succ = ell)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBethePerturbedWordTerm N c p ell eps x w sigma + sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap i.castSucc i.succ) = (c : Complex) ^ 2 * sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) * sixVertexBetheM c (sixVertexBethePhase (p (sigma i.castSucc))) * sixVertexBetheAmplitude c p sigma * sixVertexBetheWordCoefficientRemainder c (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma w i.castSucc * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordTerm_adjacent_zero_pair hc p ell hell eps heps x w i hiM hiL sigma hzero hother

/--
[sixVertexBetheZeroBoundaryPairFactor_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroBoundaryPairFactor_tendsto_eq
  {c : Real}
  {N : Nat}
  {y : Real}
-- given
  (hc : 2 < c)
  (hy : sixVertexBethePhase y ≠ 1) :
-- imply
  Tendsto (fun eps : Real => (sixVertexBetheM c (sixVertexBethePhase y) * sixVertexBetheL c (sixVertexBethePhase eps) - 1) - Complex.exp (-Complex.I * sixVertexTheta c 0 y) * sixVertexBethePhase eps ^ N * (sixVertexBetheM c (sixVertexBethePhase eps) * sixVertexBetheL c (sixVertexBethePhase y) - 1)) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * sixVertexBetheM c (sixVertexBethePhase y) * (sixVertexThetaLeftDerivAtZero c y + N))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroBoundaryPairFactor_tendsto hc hy

/--
[sum_sixVertexBethePerturbedWordTerm_adjacent_eq_zeroPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_adjacent_eq_zeroPairs_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 1)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell, (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma + sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap i.castSucc i.succ)) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_adjacent_eq_zeroPairs hc p ell eps x w i hiM hiL hother

/--
[sum_sixVertexBethePerturbedWordTerm_boundary_eq_zeroPairs](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_sixVertexBethePerturbedWordTerm_boundary_eq_zeroPairs_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hlastM : Fin.last (n + 1) ∉ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ sigma : Equiv.Perm (Fin (n + 2)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) = ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell, (sixVertexBethePerturbedWordTerm N c p ell eps x w sigma + sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap (Fin.last (n + 1)) 0)) := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBethePerturbedWordTerm_boundary_eq_zeroPairs hc p hp ell eps x w hlastM hzeroL hother

/--
[sixVertexBetheWordCoefficientRemainder_perturb_eq](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficientRemainder_perturb_eq_eq
  {n : Nat}
  {c : Real}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {eps : Real}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
  {sigma : Equiv.Perm (Fin (n + 1))}
-- given
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hzero : sigma (finRotate (n + 1) a) = ell) :
-- imply
  sixVertexBetheWordCoefficientRemainder c (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma w a = sixVertexBetheWordCoefficientRemainder c (fun j => sixVertexBethePhase (p j)) sigma w a := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficientRemainder_perturb_eq c p ell eps w a hML sigma hzero

/--
[continuous_sixVertexBethePerturbedWordMonomial](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma continuous_sixVertexBethePerturbedWordMonomial_eq
  {n N : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))} :
-- imply
  Continuous (fun eps : Real => sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma x w) := by
-- proof
  apply StatMech.FrontierD.continuous_sixVertexBethePerturbedWordMonomial p ell sigma x w

/--
[sixVertexBetheWordMonomial_erase_zero_zip_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_erase_zero_zip_adjacent_eq
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hell : p ell = 0)
  (hiL : i.castSucc ∈ w)
  (hsuccL : i.succ ∈ w)
  (hzero : sigma i.castSucc = ell) :
-- imply
  sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) (sigma * Equiv.swap i.castSucc i.succ) x (w.erase i.castSucc) = sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) sigma x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_erase_zero_zip_adjacent p ell hell sigma x w i hiL hsuccL hzero

/--
[sixVertexBetheZeroHatCoefficient_zip_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatCoefficient_zip_adjacent_eq
  {c : Real}
  {n : Nat}
  {p : Fin (n + 1) → Real}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hrot : finRotate (n + 1) a = i.castSucc)
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hiL : i.castSucc ∈ w)
  (hsuccL : i.succ ∈ w) :
-- imply
  sixVertexBetheZeroHatCoefficient c p (sigma * Equiv.swap i.castSucc i.succ) (w.erase i.castSucc) i.castSucc * sixVertexBetheL c (sixVertexBethePhase (p (sigma i.succ))) = sixVertexBetheZeroHatCoefficient c p sigma w a * sixVertexBetheM c (sixVertexBethePhase (p (sigma i.succ))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatCoefficient_zip_adjacent hc p sigma w a i hrot hML hiL hsuccL

/--
[sixVertexBetheZeroHatTerm_zip_adjacent](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatTerm_zip_adjacent_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hell : p ell = 0)
  (hrot : finRotate (n + 1) a = i.castSucc)
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hiL : i.castSucc ∈ w)
  (hsuccL : i.succ ∈ w)
  (hzero : sigma i.castSucc = ell)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBetheZeroHatTerm (N := N) c p sigma x w a = sixVertexBetheZeroHatTerm (N := N) c p (sigma * Equiv.swap i.castSucc i.succ) x (w.erase i.castSucc) i.castSucc := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatTerm_zip_adjacent hc p ell hell sigma x w a i hrot hML hiL hsuccL hzero hother

/--
[sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
-- given
  (hne : w ≠ ∅)
  (hnu : w ≠ Finset.univ) :
-- imply
  (sixVertexBetheMLBoundarySet w).Nonempty := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheMLBoundarySet_nonempty_of_nonempty_ne_univ w hne hnu

/--
[sixVertexBetheMLBoundarySet_erase_first](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheMLBoundarySet_erase_first_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
-- given
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hdL : finRotate (n + 1) (finRotate (n + 1) a) ∈ w) :
-- imply
  sixVertexBetheMLBoundarySet (w.erase (finRotate (n + 1) a)) = {finRotate (n + 1) a} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheMLBoundarySet_erase_first w a hML hdL

/--
[sixVertexBethe_erase_first_eq_empty_of_next_not_mem](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBethe_erase_first_eq_empty_of_next_not_mem_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))}
  {a : Fin (n + 1)}
-- given
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hdM : finRotate (n + 1) (finRotate (n + 1) a) ∉ w) :
-- imply
  w.erase (finRotate (n + 1) a) = ∅ := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_erase_first_eq_empty_of_next_not_mem w a hML hdM

/--
[sixVertexBetheZeroHatCoefficient_zip_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatCoefficient_zip_boundary_eq
  {c : Real}
  {n : Nat}
  {p : Fin (n + 2) → Real}
  {sigma : Equiv.Perm (Fin (n + 2))}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
-- given
  (hrot : finRotate (n + 2) a = Fin.last (n + 1))
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hlastL : Fin.last (n + 1) ∈ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w) :
-- imply
  sixVertexBetheZeroHatCoefficient c p (sigma * Equiv.swap (Fin.last (n + 1)) 0) (w.erase (Fin.last (n + 1))) (Fin.last (n + 1)) * sixVertexBetheL c (sixVertexBethePhase (p (sigma 0))) = sixVertexBetheZeroHatCoefficient c p sigma w a * sixVertexBetheM c (sixVertexBethePhase (p (sigma 0))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatCoefficient_zip_boundary p sigma w a hrot hML hlastL hzeroL

/--
[sixVertexBetheWordMonomial_erase_zero_zip_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_erase_zero_zip_boundary_eq
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {sigma : Equiv.Perm (Fin (n + 2))}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
-- given
  (hell : p ell = 0)
  (hlastL : Fin.last (n + 1) ∈ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (hroot : sigma (Fin.last (n + 1)) = ell) :
-- imply
  sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) (sigma * Equiv.swap (Fin.last (n + 1)) 0) x (w.erase (Fin.last (n + 1))) = sixVertexBethePhase (p (sigma 0)) ^ N * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) sigma x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_erase_zero_zip_boundary p ell hell sigma x w hlastL hzeroL hroot

/--
[sixVertexBetheZeroHatTerm_zip_boundary](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatTerm_zip_boundary_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {sigma : Equiv.Perm (Fin (n + 2))}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hrot : finRotate (n + 2) a = Fin.last (n + 1))
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hlastL : Fin.last (n + 1) ∈ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (hroot : sigma (Fin.last (n + 1)) = ell)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBetheZeroHatTerm (N := N) c p sigma x w a = sixVertexBetheZeroHatTerm (N := N) c p (sigma * Equiv.swap (Fin.last (n + 1)) 0) x (w.erase (Fin.last (n + 1))) (Fin.last (n + 1)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatTerm_zip_boundary hc p hp ell hell sigma x w a hrot hML hlastL hzeroL hroot hother

/--
[sixVertexBetheZeroHatTerm_singleton](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatTerm_singleton_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {sigma : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → Int}
  {a s : Fin (n + 1)}
-- given
  (hell : p ell = 0)
  (hrot : finRotate (n + 1) a = s)
  (has : a ≠ s)
  (hroot : sigma s = ell) :
-- imply
  sixVertexBetheZeroHatTerm (N := N) c p sigma x {s} a = (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexBetheAmplitude c p sigma * sixVertexBetheIntMonomial p sigma x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatTerm_singleton p ell hell sigma x a s hrot has hroot

/--
[sixVertexBetheZeroHatTerm_normalize](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatTerm_normalize_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {sigma : Equiv.Perm (Fin (n + 2))}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hroot : sigma (finRotate (n + 2) a) = ell)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∃ t, ∃ rho : Equiv.Perm (Fin (n + 2)), t ∈ w ∧ rho t = ell ∧ (∀ k, k ∉ w → rho k = sigma k) ∧ sixVertexBetheZeroHatTerm (N := N) c p sigma x w a = (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexBetheAmplitude c p rho * sixVertexBetheIntMonomial p rho x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatTerm_normalize hc p hp ell hell sigma x w a hML hroot hother

/--
[sixVertexBetheZeroHatTerm_normalize_mulRight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheZeroHatTerm_normalize_mulRight_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∃ t, ∃ tau : Equiv.Perm (Fin (n + 2)), t ∈ w ∧ finRotate (n + 2) t ∉ w ∧ (∀ u, u ∈ w → finRotate (n + 2) u ∉ w → u = t) ∧ tau t = finRotate (n + 2) a ∧ (∀ k, k ∉ w → tau k = k) ∧ ∀ sigma : Equiv.Perm (Fin (n + 2)), sigma (finRotate (n + 2) a) = ell → sixVertexBetheZeroHatTerm (N := N) c p sigma x w a = (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexBetheAmplitude c p (sigma * tau) * sixVertexBetheIntMonomial p (sigma * tau) x := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheZeroHatTerm_normalize_mulRight hc p hp ell hell x w a hML hother

/--
[sum_sixVertexBetheZeroHatTerm_eq_terminal](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_sixVertexBetheZeroHatTerm_eq_terminal_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {a : Fin (n + 2)}
  {F : Fin (n + 2) → Complex}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∃ t ∈ w, finRotate (n + 2) t ∉ w ∧ (∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma (finRotate (n + 2) a) = ell, F (sigma a) * sixVertexBetheZeroHatTerm (N := N) c p sigma x w a) = (∏ j ∈ (Finset.univ.erase ell), sixVertexBetheM c (sixVertexBethePhase (p j))) * ∑ rho : Equiv.Perm (Fin (n + 2)) with rho t = ell, F (rho a) * sixVertexBetheAmplitude c p rho * sixVertexBetheIntMonomial p rho x := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheZeroHatTerm_eq_terminal hc p hp ell hell x w a hML hother F

/--
[mem_sixVertexBetheCyclicWord](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma mem_sixVertexBetheCyclicWord_eq
  {m : Nat}
  {a t k : Fin (m + 1)} :
-- imply
  k ∈ sixVertexBetheCyclicWord a t ↔ 0 < (k - a).val ∧ (k - a).val ≤ (t - a).val := by
-- proof
  apply StatMech.FrontierD.mem_sixVertexBetheCyclicWord a t k

/--
[sixVertexBetheCyclicWord_MLBoundarySet](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheCyclicWord_MLBoundarySet_eq
  {m : Nat}
  {a t : Fin (m + 1)}
-- given
  (hat : a ≠ t) :
-- imply
  sixVertexBetheMLBoundarySet (sixVertexBetheCyclicWord a t) = {a} := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCyclicWord_MLBoundarySet a t hat

/--
[sixVertexBetheCyclicWord_unique_LM](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheCyclicWord_unique_LM_eq
  {m : Nat}
  {a t : Fin (m + 1)}
-- given
  (hat : a ≠ t) :
-- imply
  t ∈ sixVertexBetheCyclicWord a t ∧ finRotate (m + 1) t ∉ sixVertexBetheCyclicWord a t ∧ ∀ u, u ∈ sixVertexBetheCyclicWord a t → finRotate (m + 1) u ∉ sixVertexBetheCyclicWord a t → u = t := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheCyclicWord_unique_LM a t hat

/--
[eq_sixVertexBetheCyclicWord_of_boundaries](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma eq_sixVertexBetheCyclicWord_of_boundaries_eq
  {m : Nat}
  {w : Finset (Fin (m + 1))}
  {a t : Fin (m + 1)}
-- given
  (hML : sixVertexBetheMLBoundarySet w = {a})
  (htmem : t ∈ w)
  (htend : finRotate (m + 1) t ∉ w)
  (htUnique : ∀ u, u ∈ w → finRotate (m + 1) u ∉ w → u = t) :
-- imply
  w = sixVertexBetheCyclicWord a t := by
-- proof
  apply StatMech.FrontierD.eq_sixVertexBetheCyclicWord_of_boundaries w a t hML htmem htend htUnique

/--
[sixVertexBethePerturbedWordSum_adjacent_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordSum_adjacent_tendsto_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 1) → Real}
  {ell : Fin (n + 1)}
  {x : Fin (n + 1) → Int}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hell : p ell = 0)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hML : sixVertexBetheMLBoundarySet w = {i.castSucc})
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (fun eps : Real => ∑ sigma : Equiv.Perm (Fin (n + 1)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * ∑ sigma : Equiv.Perm (Fin (n + 1)) with sigma i.succ = ell, sixVertexThetaLeftDerivAtZero c (p (sigma i.castSucc)) * sixVertexBetheZeroHatTerm (N := N) c p sigma x w i.castSucc)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordSum_adjacent_tendsto hc p ell hell x w i hiM hiL hML hother

/--
[sixVertexBethePerturbedWordTerm_boundary_zero_pair](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordTerm_boundary_zero_pair_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {eps : Real}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
  {sigma : Equiv.Perm (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hlastM : Fin.last (n + 1) ∉ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (hroot : sigma 0 = ell) :
-- imply
  sixVertexBethePerturbedWordTerm N c p ell eps x w sigma + sixVertexBethePerturbedWordTerm N c p ell eps x w (sigma * Equiv.swap (Fin.last (n + 1)) 0) = ((sixVertexBetheM c (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) * sixVertexBetheL c (sixVertexBethePhase eps) - 1) - Complex.exp (-Complex.I * sixVertexTheta c 0 (p (sigma (Fin.last (n + 1))))) * sixVertexBethePhase eps ^ N * (sixVertexBetheM c (sixVertexBethePhase eps) * sixVertexBetheL c (sixVertexBethePhase (p (sigma (Fin.last (n + 1))))) - 1)) * sixVertexBetheAmplitude c p sigma * sixVertexBetheWordCoefficientRemainder c (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma w (Fin.last (n + 1)) * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (sixVertexBethePerturbRoot p ell eps j)) sigma x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordTerm_boundary_zero_pair hc p hp ell hell eps x w hlastM hzeroL sigma hroot

/--
[sixVertexBethePerturbedWordSum_boundary_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBethePerturbedWordSum_boundary_tendsto_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
  {w : Finset (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hlastM : Fin.last (n + 1) ∉ w)
  (hzeroL : (0 : Fin (n + 2)) ∈ w)
  (hML : sixVertexBetheMLBoundarySet w = {Fin.last (n + 1)})
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (fun eps : Real => ∑ sigma : Equiv.Perm (Fin (n + 2)), sixVertexBethePerturbedWordTerm N c p ell eps x w sigma) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma 0 = ell, (sixVertexThetaLeftDerivAtZero c (p (sigma (Fin.last (n + 1)))) + N) * sixVertexBetheZeroHatTerm (N := N) c p sigma x w (Fin.last (n + 1)))) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethePerturbedWordSum_boundary_tendsto hc p hp ell hell x w hlastM hzeroL hML hother

/--
[sum_singleMLWords_eq_cyclicWords](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_singleMLWords_eq_cyclicWords_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
  {f : Finset (Fin (n + 2)) → Complex}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ w : Finset (Fin (n + 2)) with (sixVertexBetheMLBoundarySet w).card = 1, f w) = ∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a, f (sixVertexBetheCyclicWord a t) := by
-- proof
  apply StatMech.FrontierD.sum_singleMLWords_eq_cyclicWords hc p hp ell hell x hother f

/--
[sum_marked_zero_slot](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_marked_zero_slot_eq
  {m : Nat}
  {ell : Fin (m + 1)}
  {F : Fin (m + 1) → Complex}
  {W : Equiv.Perm (Fin (m + 1)) → Complex} :
-- imply
  (∑ a : Fin (m + 1), ∑ t : Fin (m + 1) with t ≠ a, ∑ rho : Equiv.Perm (Fin (m + 1)) with rho t = ell, F (rho a) * W rho) = (∑ j : Fin (m + 1) with j ≠ ell, F j) * ∑ rho, W rho := by
-- proof
  apply StatMech.FrontierD.sum_marked_zero_slot ell F W

/--
[sum_zero_slot_except_last](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_zero_slot_except_last_eq
  {m : Nat}
  {ell : Fin (m + 1)}
  {W : Equiv.Perm (Fin (m + 1)) → Complex} :
-- imply
  (∑ t : Fin (m + 1) with t ≠ Fin.last m, ∑ rho : Equiv.Perm (Fin (m + 1)) with rho t = ell, W rho) = (∑ rho, W rho) - ∑ rho : Equiv.Perm (Fin (m + 1)) with rho (Fin.last m) = ell, W rho := by
-- proof
  apply StatMech.FrontierD.sum_zero_slot_except_last ell W

/--
[sum_singleML_zeroHatTerms](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sum_singleML_zeroHatTerms_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ a : Fin (n + 2), ∑ t : Fin (n + 2) with t ≠ a, (c : Complex) ^ 2 * ∑ sigma : Equiv.Perm (Fin (n + 2)) with sigma (finRotate (n + 2) a) = ell, (sixVertexThetaLeftDerivAtZero c (p (sigma a)) + if a = Fin.last (n + 1) then N else 0) * sixVertexBetheZeroHatTerm (N := N) c p sigma x (sixVertexBetheCyclicWord a t) a) = (c : Complex) ^ 2 * (((N : Complex) + ∑ j ∈ Finset.univ.erase ell, (sixVertexThetaLeftDerivAtZero c (p j) : Complex)) * (∏ j ∈ Finset.univ.erase ell, sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexCoordinateBetheIntWave c p x - (N : Complex) * (∏ j ∈ Finset.univ.erase ell, sixVertexBetheM c (sixVertexBethePhase (p j))) * ∑ rho : Equiv.Perm (Fin (n + 2)) with rho (Fin.last (n + 1)) = ell, sixVertexBetheAmplitude c p rho * sixVertexBetheIntMonomial p rho x) := by
-- proof
  apply StatMech.FrontierD.sum_singleML_zeroHatTerms hc p hp ell hell x hother

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedSingleMLWordTotal_tendsto](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma perturbedSingleMLWordTotal_tendsto_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (sixVertexBethePerturbedSingleMLWordTotal N c p ell x) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds ((c : Complex) ^ 2 * (((N : Complex) + ∑ j ∈ Finset.univ.erase ell, (sixVertexThetaLeftDerivAtZero c (p j) : Complex)) * (∏ j ∈ Finset.univ.erase ell, sixVertexBetheM c (sixVertexBethePhase (p j))) * sixVertexCoordinateBetheIntWave c p x - (N : Complex) * (∏ j ∈ Finset.univ.erase ell, sixVertexBetheM c (sixVertexBethePhase (p j))) * ∑ rho : Equiv.Perm (Fin (n + 2)) with rho (Fin.last (n + 1)) = ell, sixVertexBetheAmplitude c p rho * sixVertexBetheIntMonomial p rho x))) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedSingleMLWordTotal_tendsto hc p hp ell hell hother x

/--
[sixVertexBetheMLBoundarySet_card_eq_zero_iff](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexBetheMLBoundarySet_card_eq_zero_iff_eq
  {n : Nat}
  {w : Finset (Fin (n + 1))} :
-- imply
  (sixVertexBetheMLBoundarySet w).card = 0 ↔ w = ∅ ∨ w = Finset.univ := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheMLBoundarySet_card_eq_zero_iff w

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_eq_constant_add_single](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma perturbedWordTotal_eq_constant_add_single_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
  {eps : Real}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBethePerturbedWordTotal N c p ell x eps = sixVertexBethePerturbedConstantWordTotal N c p ell x eps + sixVertexBethePerturbedSingleMLWordTotal N c p ell x eps := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_eq_constant_add_single hc p hp ell hother x eps

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_zeroPhaseEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma perturbedWordTotal_tendsto_zeroPhaseEigenvalue_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
  {x : Fin (n + 2) → Int}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  Tendsto (sixVertexBethePerturbedWordTotal N c p ell x) (nhdsWithin (0 : Real) (Set.singleton (0 : Real))ᶜ) (nhds (sixVertexZeroPhaseBetheEigenvalueCandidate c N p ell * sixVertexCoordinateBetheIntWave c p x)) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.perturbedWordTotal_tendsto_zeroPhaseEigenvalue hc p hp ell hell hother x

/--
[sixVertexCoordinateBetheZeroPhaseEigenrelation](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexCoordinateBetheZeroPhaseEigenrelation_eq
  {c : Real}
  {N n : Nat}
  {p : Fin (n + 2) → Real}
  {ell : Fin (n + 2)}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hell : p ell = 0)
  (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell := by
-- proof
  apply StatMech.FrontierD.sixVertexCoordinateBetheZeroPhaseEigenrelation hc p hp ell hell hopen hother

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseEigenrelation_of_two_le](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma physicalZeroPhaseEigenrelation_of_two_le_eq
  {c : Real}
  {N n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hn : 2 ≤ n)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N n p)
  (hell : p ell = 0)
  (hopen : ∀ j, p j ∈ Set.Ioo (-Real.pi) Real.pi)
  (hother : ∀ j, j ≠ ell → sixVertexBethePhase (p j) ≠ 1) :
-- imply
  SixVertexCoordinateBetheZeroPhaseEigenrelation (N := N) c p ell := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.physicalZeroPhaseEigenrelation_of_two_le hc hn p hp ell hell hopen hother

/--
[sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric_eq
  {c : Real}
  {n : Nat}
  {p : Fin n → Real}
  {ell : Fin n}
-- given
  (hc : 2 < c)
  (hsymm : ∀ j, p j.rev = -p j)
  (hellrev : ell.rev = ell)
  (hunique : ∀ j, p j = 0 → j = ell) :
-- imply
  (∏ j ∈ Finset.univ.erase ell, sixVertexBetheM c (sixVertexBethePhase (p j))) = ((∏ j ∈ Finset.univ.erase ell, ‖sixVertexBetheM c (sixVertexBethePhase (p j))‖ : Real) : Complex) := by
-- proof
  apply StatMech.FrontierD.sixVertexZeroPhaseMProduct_eq_normProduct_of_symmetric hc p ell hsymm hellrev hunique

/--
[sixVertexFixedChargeBetheRoots_physicalZeroPhaseEigenrelation_of_odd_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_physicalZeroPhaseEigenrelation_of_odd_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  SixVertexCoordinateBetheZeroPhaseEigenrelation (N := sixVertexFourWidth r k) c (sixVertexFixedChargeBetheRoots hc r k) (sixVertexFixedChargeBetheCentralIndex r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_physicalZeroPhaseEigenrelation_of_odd_charge hc hr k

/--
[sixVertexFixedOddChargeBetheEigenvalueCandidate_eq_value](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexFixedOddChargeBetheEigenvalueCandidate_eq_value_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  sixVertexFixedOddChargeBetheEigenvalueCandidate hc r k = (sixVertexFixedOddChargeBetheEigenvalueValue hc r k : Complex) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedOddChargeBetheEigenvalueCandidate_eq_value hc hr k

/--
[sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheZeroPhaseSingle.lean)
-/
@[path]
private lemma sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge_eq
  {c : Real}
  {r : Nat}
  {k : Nat}
-- given
  (hc : 2 < c)
  (hr : Odd r) :
-- imply
  (sixVertexSectorTransferComplex (sixVertexFourWidth r k) (sixVertexFixedChargeBetheParticleCount r k) c).mulVec (sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k)) = (sixVertexFixedOddChargeBetheEigenvalueValue hc r k : Complex) • sixVertexCoordinateBetheWave c (sixVertexFixedChargeBetheRoots hc r k) := by
-- proof
  apply StatMech.FrontierD.sixVertexFixedChargeBetheRoots_zeroPhaseEigenrelation_value_of_odd_charge hc hr k


-- created on 2026-10-23
