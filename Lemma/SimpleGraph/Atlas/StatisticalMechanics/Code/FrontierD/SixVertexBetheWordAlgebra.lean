import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.StatisticalMechanics.Code.FrontierD.SixVertexBetheWordAlgebra.Part3
open StatMech StatMech.FrontierD


/--
[sum_perm_eq_zero_of_mul_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_perm_eq_zero_of_mul_neg_eq
  {n : ℕ}
  {τ : Equiv.Perm (Fin n)}
  {f : Equiv.Perm (Fin n) → ℂ}
-- given
  (hmul : ∀ σ, f (σ * τ) = -f σ) :
-- imply
  ∑ σ, f σ = 0 := by
-- proof
  apply StatMech.FrontierD.sum_perm_eq_zero_of_mul_neg τ f hmul

/--
[sum_perm_eq_zero_of_swap_neg](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_perm_eq_zero_of_swap_neg_eq
  {n : ℕ}
  {i j : Fin n}
  {f : Equiv.Perm (Fin n) → ℂ}
-- given
  (hswap : ∀ σ, f (σ * Equiv.swap i j) = -f σ) :
-- imply
  ∑ σ, f σ = 0 := by
-- proof
  apply StatMech.FrontierD.sum_perm_eq_zero_of_swap_neg i j f hswap

/--
[sixVertexBetheM_mul_L_sub_one](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheM_mul_L_sub_one_eq
  {c : ℝ}
  {z w : ℂ}
-- given
  (hc : 2 < c)
  (hz : z ≠ 1)
  (hw : w ≠ 1) :
-- imply
  sixVertexBetheM c z * sixVertexBetheL c w - 1 = -((c : ℂ) ^ 2) * sixVertexBethePairFactor c w z / ((1 - z) * (1 - w)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_mul_L_sub_one hc hz hw

/--
[sixVertexBethe_geometricInterval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBethe_geometricInterval_eq
  {c : ℝ}
  {z : ℂ}
  {a b : ℕ}
-- given
  (hz : z ≠ 1)
  (hab : a < b) :
-- imply
  z ^ a + (c : ℂ) ^ 2 * (∑ y ∈ Finset.Ioo a b, z ^ y) + z ^ b = sixVertexBetheL c z * z ^ a + sixVertexBetheM c z * z ^ b := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_geometricInterval c hz hab

/--
[sixVertexBethe_relaxedWordExpansion](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBethe_relaxedWordExpansion_eq
  {c : ℝ}
  {n : ℕ}
  {z : Fin n → ℂ}
  {a b : Fin n → ℕ}
-- given
  (hz : ∀ k, z k ≠ 1)
  (hab : ∀ k, a k < b k) :
-- imply
  (∏ k, ((z k) ^ (a k) + (c : ℂ) ^ 2 * (∑ y ∈ Finset.Ioo (a k) (b k), (z k) ^ y) + (z k) ^ (b k))) = ∑ w : Finset (Fin n), (∏ k ∈ w, sixVertexBetheL c (z k) * (z k) ^ (a k)) * ∏ k ∈ wᶜ, sixVertexBetheM c (z k) * (z k) ^ (b k) := by
-- proof
  apply StatMech.FrontierD.sixVertexBethe_relaxedWordExpansion c z a b hz hab

/--
[sixVertexBetheIntMonomial_rotate](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheIntMonomial_rotate_eq
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → ℤ} :
-- imply
  sixVertexBetheIntMonomial p (σ * finRotate (n + 1)) x = sixVertexBethePhase (p (σ 0)) ^ N * sixVertexBetheIntMonomial p σ (sixVertexBetheShiftCoordinates N x) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheIntMonomial_rotate p σ x

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.changeVariables](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma changeVariables_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {f : Equiv.Perm (Fin (n + 1)) → ℂ}
  {x : Fin (n + 1) → ℤ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * f σ * sixVertexBetheIntMonomial p σ x = ∑ σ, sixVertexBetheAmplitude c p σ * f (σ * finRotate (n + 1)) * sixVertexBetheIntMonomial p σ (sixVertexBetheShiftCoordinates N x) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.changeVariables hc hp f x

/--
[sixVertexBetheWordCoefficient_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficient_empty_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))} :
-- imply
  sixVertexBetheWordCoefficient c z σ ∅ = ∏ i, sixVertexBetheM c (z (σ i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficient_empty c z σ

/--
[sixVertexBetheWordCoefficient_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficient_univ_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))} :
-- imply
  sixVertexBetheWordCoefficient c z σ Finset.univ = ∏ i, sixVertexBetheL c (z (σ i)) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficient_univ c z σ

/--
[sixVertexBetheWordMonomial_empty](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_empty_eq
  {n : ℕ}
  {N : ℕ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → ℤ} :
-- imply
  sixVertexBetheWordMonomial N z σ x ∅ = ∏ i, z (σ i) ^ x i := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_empty N z σ x

/--
[sixVertexBetheWordMonomial_univ](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_univ_eq
  {n : ℕ}
  {N : ℕ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → ℤ} :
-- imply
  sixVertexBetheWordMonomial N z σ x Finset.univ = ∏ i, z (σ i) ^ (sixVertexBetheShiftCoordinates N x i) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_univ N z σ x

/--
[sixVertexBetheWordCoefficientRemainder_swap_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficientRemainder_swap_invariant_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {a b : Fin (n + 1)}
-- given
  (haM : a ∉ w)
  (hbL : b ∈ w)
  (hab : finRotate (n + 1) a = b) :
-- imply
  sixVertexBetheWordCoefficientRemainder c z (σ * Equiv.swap a b) w a = sixVertexBetheWordCoefficientRemainder c z σ w a := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficientRemainder_swap_invariant c z σ w haM hbL hab

/--
[sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {a b : Fin (n + 1)}
-- given
  (haM : a ∉ w)
  (hbL : b ∈ w)
  (hab : finRotate (n + 1) a = b) :
-- imply
  sixVertexBetheWordCoefficient c z σ w = (sixVertexBetheM c (z (σ a)) * sixVertexBetheL c (z (σ b)) - 1) * sixVertexBetheWordCoefficientRemainder c z σ w a := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficient_eq_cyclic_ML_mul_remainder c z σ w haM hbL hab

/--
[sixVertexBetheWordCoefficientRemainder_adjacent_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficientRemainder_adjacent_invariant_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w) :
-- imply
  sixVertexBetheWordCoefficientRemainder c z (σ * Equiv.swap i.castSucc i.succ) w i.castSucc = sixVertexBetheWordCoefficientRemainder c z σ w i.castSucc := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficientRemainder_adjacent_invariant c z σ w i hiM hiL

/--
[sixVertexBetheWordCoefficient_eq_ML_mul_remainder](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordCoefficient_eq_ML_mul_remainder_eq
  {n : ℕ}
  {c : ℝ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w) :
-- imply
  sixVertexBetheWordCoefficient c z σ w = (sixVertexBetheM c (z (σ i.castSucc)) * sixVertexBetheL c (z (σ i.succ)) - 1) * sixVertexBetheWordCoefficientRemainder c z σ w i.castSucc := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordCoefficient_eq_ML_mul_remainder c z σ w i hiM hiL

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.intWave_shift](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma intWave_shift_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {x : Fin (n + 1) → ℤ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  sixVertexCoordinateBetheIntWave c p x = sixVertexCoordinateBetheIntWave c p (sixVertexBetheShiftCoordinates N x) := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.intWave_shift hc hp x

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.constantWordContribution](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma constantWordContribution_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {x : Fin (n + 1) → ℤ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p) :
-- imply
  (∑ σ, sixVertexBetheAmplitude c p σ * (((∏ k, sixVertexBetheL c (sixVertexBethePhase (p (σ k)))) * sixVertexBetheIntMonomial p σ (sixVertexBetheShiftCoordinates N x)) + ((∏ k, sixVertexBetheM c (sixVertexBethePhase (p (σ k)))) * sixVertexBetheIntMonomial p σ x))) = sixVertexBetheEigenvalueCandidate c p * sixVertexCoordinateBetheIntWave c p x := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.constantWordContribution hc hp x

/--
[sixVertexBetheM_mul_L_sub_one_ne_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheM_mul_L_sub_one_ne_zero_eq
  {c : ℝ}
  {p q : ℝ}
-- given
  (hc : 2 < c)
  (hp : sixVertexBethePhase p ≠ 1)
  (hq : sixVertexBethePhase q ≠ 1) :
-- imply
  sixVertexBetheM c (sixVertexBethePhase q) * sixVertexBetheL c (sixVertexBethePhase p) - 1 ≠ 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheM_mul_L_sub_one_ne_zero hc hp hq

/--
[sixVertexTheta_exp_eq_ML_ratio](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexTheta_exp_eq_ML_ratio_eq
  {c : ℝ}
  {p q : ℝ}
-- given
  (hc : 2 < c)
  (hp : sixVertexBethePhase p ≠ 1)
  (hq : sixVertexBethePhase q ≠ 1) :
-- imply
  Complex.exp (Complex.I * sixVertexTheta c p q) = (sixVertexBetheM c (sixVertexBethePhase p) * sixVertexBetheL c (sixVertexBethePhase q) - 1) / (sixVertexBetheM c (sixVertexBethePhase q) * sixVertexBetheL c (sixVertexBethePhase p) - 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexTheta_exp_eq_ML_ratio hc hp hq

/--
[sixVertexBetheAmplitude_adjacent_ML_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_adjacent_ML_cancel_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (ha : sixVertexBethePhase (p (σ i.castSucc)) ≠ 1)
  (hb : sixVertexBethePhase (p (σ i.succ)) ≠ 1) :
-- imply
  sixVertexBetheAmplitude c p (σ * Equiv.swap i.castSucc i.succ) * (sixVertexBetheM c (sixVertexBethePhase (p (σ i.succ))) * sixVertexBetheL c (sixVertexBethePhase (p (σ i.castSucc))) - 1) = -sixVertexBetheAmplitude c p σ * (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) * sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_adjacent_ML_cancel hc p σ i ha hb

/--
[sum_sixVertexBetheAmplitude_adjacent_ML_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_sixVertexBetheAmplitude_adjacent_ML_eq_zero_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {i : Fin n}
  {B : Equiv.Perm (Fin (n + 1)) → ℂ}
-- given
  (hc : 2 < c)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1)
  (hB : ∀ σ, B (σ * Equiv.swap i.castSucc i.succ) = B σ) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * (sixVertexBetheM c (sixVertexBethePhase (p (σ i.castSucc))) * sixVertexBetheL c (sixVertexBethePhase (p (σ i.succ))) - 1) * B σ = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheAmplitude_adjacent_ML_eq_zero hc p i B hphase hB

/--
[sixVertexBetheAmplitude_wordCoefficient_adjacent_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_wordCoefficient_adjacent_cancel_eq
  {c : ℝ}
  {n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  sixVertexBetheAmplitude c p (σ * Equiv.swap i.castSucc i.succ) * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) (σ * Equiv.swap i.castSucc i.succ) w = -(sixVertexBetheAmplitude c p σ * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w) := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_wordCoefficient_adjacent_cancel hc p σ w i hiM hiL hphase

/--
[sixVertexBetheWordMonomial_adjacent_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_adjacent_invariant_eq
  {N n : ℕ}
  {z : Fin (n + 1) → ℂ}
  {σ : Equiv.Perm (Fin (n + 1))}
  {x : Fin (n + 1) → ℤ}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w) :
-- imply
  sixVertexBetheWordMonomial N z (σ * Equiv.swap i.castSucc i.succ) x w = sixVertexBetheWordMonomial N z σ x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_adjacent_invariant z σ x w i hiM hiL

/--
[sixVertexBetheWordMonomial_boundary_covariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheWordMonomial_boundary_covariant_eq
  {N n : ℕ}
  {z : Fin (n + 2) → ℂ}
  {σ : Equiv.Perm (Fin (n + 2))}
  {x : Fin (n + 2) → ℤ}
  {w : Finset (Fin (n + 2))}
-- given
  (hz : ∀ k, z k ≠ 0)
  (haM : Fin.last (n + 1) ∉ w)
  (hbL : (0 : Fin (n + 2)) ∈ w) :
-- imply
  z (σ (Fin.last (n + 1))) ^ N * sixVertexBetheWordMonomial N z (σ * Equiv.swap (Fin.last (n + 1)) 0) x w = z (σ 0) ^ N * sixVertexBetheWordMonomial N z σ x w := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheWordMonomial_boundary_covariant z hz σ x w haM hbL

/--
[sum_sixVertexBetheWordTerm_adjacent_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_sixVertexBetheWordTerm_adjacent_eq_zero_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {x : Fin (n + 1) → ℤ}
  {w : Finset (Fin (n + 1))}
  {i : Fin n}
-- given
  (hc : 2 < c)
  (hiM : i.castSucc ∉ w)
  (hiL : i.succ ∈ w)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheWordTerm_adjacent_eq_zero hc p x w i hiM hiL hphase

/--
[sixVertexBetheAmplitude_boundary_ML_cancel](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheAmplitude_boundary_ML_cancel_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 2) → ℝ}
  {σ : Equiv.Perm (Fin (n + 2))}
  {B : Equiv.Perm (Fin (n + 2)) → ℂ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (ha : sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ≠ 1)
  (hb : sixVertexBethePhase (p (σ 0)) ≠ 1)
  (hB : sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N * B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2))) = sixVertexBethePhase (p (σ 0)) ^ N * B σ) :
-- imply
  sixVertexBetheAmplitude c p (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2))) * (sixVertexBetheM c (sixVertexBethePhase (p (σ 0))) * sixVertexBetheL c (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) - 1) * B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2))) = -sixVertexBetheAmplitude c p σ * (sixVertexBetheM c (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) * sixVertexBetheL c (sixVertexBethePhase (p (σ 0))) - 1) * B σ := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheAmplitude_boundary_ML_cancel hc p hp σ B ha hb hB

/--
[sum_sixVertexBetheAmplitude_boundary_ML_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_sixVertexBetheAmplitude_boundary_ML_eq_zero_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 2) → ℝ}
  {B : Equiv.Perm (Fin (n + 2)) → ℂ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1)
  (hB : ∀ σ, sixVertexBethePhase (p (σ (Fin.last (n + 1)))) ^ N * B (σ * ((finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2))) = sixVertexBethePhase (p (σ 0)) ^ N * B σ) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * (sixVertexBetheM c (sixVertexBethePhase (p (σ (Fin.last (n + 1))))) * sixVertexBetheL c (sixVertexBethePhase (p (σ 0))) - 1) * B σ = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheAmplitude_boundary_ML_eq_zero hc p hp B hphase hB

/--
[sixVertexBetheBoundaryPermutation_eq_swap](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sixVertexBetheBoundaryPermutation_eq_swap_eq
  {n : ℕ} :
-- imply
  (finRotate (n + 2)).symm * Equiv.swap 0 1 * finRotate (n + 2) = Equiv.swap (Fin.last (n + 1)) 0 := by
-- proof
  apply StatMech.FrontierD.sixVertexBetheBoundaryPermutation_eq_swap n

/--
[sum_sixVertexBetheWordTerm_boundary_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_sixVertexBetheWordTerm_boundary_eq_zero_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 2) → ℝ}
  {x : Fin (n + 2) → ℤ}
  {w : Finset (Fin (n + 2))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 2) p)
  (haM : Fin.last (n + 1) ∉ w)
  (hbL : (0 : Fin (n + 2)) ∈ w)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheWordTerm_boundary_eq_zero hc p hp x w haM hbL hphase

/--
[exists_sixVertexBetheCyclic_ML_of_nonconstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma exists_sixVertexBetheCyclic_ML_of_nonconstant_eq
  {n : ℕ}
  {w : Finset (Fin (n + 1))}
-- given
  (hne : w ≠ ∅)
  (hnu : w ≠ Finset.univ) :
-- imply
  (∃ i : Fin n, i.castSucc ∉ w ∧ i.succ ∈ w) ∨ (Fin.last n ∉ w ∧ (0 : Fin (n + 1)) ∈ w) := by
-- proof
  apply StatMech.FrontierD.exists_sixVertexBetheCyclic_ML_of_nonconstant w hne hnu

/--
[sum_sixVertexBetheWordTerm_eq_zero_of_nonconstant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma sum_sixVertexBetheWordTerm_eq_zero_of_nonconstant_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {x : Fin (n + 1) → ℤ}
  {w : Finset (Fin (n + 1))}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hne : w ≠ ∅)
  (hnu : w ≠ Finset.univ)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  ∑ σ, sixVertexBetheAmplitude c p σ * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) σ x w = 0 := by
-- proof
  apply StatMech.FrontierD.sum_sixVertexBetheWordTerm_eq_zero_of_nonconstant hc p hp x w hne hnu hphase

/--
[SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierD/SixVertexBetheWordAlgebra.lean)
-/
@[path]
private lemma cyclicWordEigenvalue_eq
  {c : ℝ}
  {N n : ℕ}
  {p : Fin (n + 1) → ℝ}
  {x : Fin (n + 1) → ℤ}
-- given
  (hc : 2 < c)
  (hp : SixVertexSatisfiesMultiplicativeBetheEquations c N (n + 1) p)
  (hphase : ∀ j, sixVertexBethePhase (p j) ≠ 1) :
-- imply
  (∑ w : Finset (Fin (n + 1)), ∑ σ, sixVertexBetheAmplitude c p σ * sixVertexBetheWordCoefficient c (fun j => sixVertexBethePhase (p j)) σ w * sixVertexBetheWordMonomial N (fun j => sixVertexBethePhase (p j)) σ x w) = sixVertexBetheEigenvalueCandidate c p * sixVertexCoordinateBetheIntWave c p x := by
-- proof
  apply StatMech.FrontierD.SixVertexSatisfiesMultiplicativeBetheEquations.cyclicWordEigenvalue hc p hp x hphase


-- created on 2026-10-23
