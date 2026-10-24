import Mathlib
import sympy.Basic
import sympy.atlas.StatisticalMechanics.Code.FrontierA.AnisotropicSquareTorusKacWard
open StatMech StatMech.FrontierA


/--
[ons_weightedRootIdentity_unconditional](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma ons_weightedRootIdentity_unconditional_eq
  {L : Nat}
  [Fact (2 < L)] :
-- imply
  ons_weightedRootIdentity L := by
-- proof
  apply StatMech.FrontierA.ons_weightedRootIdentity_unconditional L

/--
[squareTorusWeightedSpinScalePolynomial_eval](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma squareTorusWeightedSpinScalePolynomial_eval_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Complex}
  {a b : Fin 2}
  {t : Complex} :
-- imply
  (squareTorusWeightedSpinScalePolynomial L weight a b).eval t = ons_weightedSpinCharacterSum L (fun edge ↦ t * weight edge) a b := by
-- proof
  apply StatMech.FrontierA.squareTorusWeightedSpinScalePolynomial_eval L weight a b t

/--
[squareTorus_weightedSpin_sq_eq_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma squareTorus_weightedSpin_sq_eq_det_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Complex}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L weight a b ^ 2 = (1 - ons_KWmatWeightedPhase L weight ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.FrontierA.squareTorus_weightedSpin_sq_eq_det L weight a b

/--
[anisotropicSquareKWSymbolMatrix_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWSymbolMatrix_det_eq
  {x y omega z₁ z₂ : Complex}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hz₁ : z₁ ≠ 0)
  (hz₂ : z₂ ≠ 0) :
-- imply
  (anisotropicSquareKWSymbolMatrix x y omega z₁ z₂).det = (1 + x ^ 2) * (1 + y ^ 2) - x * (1 - y ^ 2) * (z₁ + z₁⁻¹) - y * (1 - x ^ 2) * (z₂ + z₂⁻¹) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWSymbolMatrix_det x y omega z₁ z₂ homega hz₁ hz₂

/--
[anisotropicSquareKWSymbolMatrix_det_cos](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWSymbolMatrix_det_cos_eq
  {x y k₁ k₂ : Real} :
-- imply
  (anisotropicSquareKWSymbolMatrix (x : Complex) (y : Complex) ons_turnRoot (Complex.exp (Complex.I * k₁)) (Complex.exp (Complex.I * k₂))).det = (anisotropicSquareHighTempSymbol x y k₁ k₂ : Complex) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWSymbolMatrix_det_cos x y k₁ k₂

/--
[anisotropicSquareKWMatrixPhase_translation_invariant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWMatrixPhase_translation_invariant_eq
  {L : Nat}
  {x y omega u v : Complex}
  {t : ZMod L × ZMod L}
  {d₁ d₂ : ons_Dart L} :
-- imply
  anisotropicSquareKWMatrixPhase L x y omega u v (ons_shiftDart L t d₂) (ons_shiftDart L t d₁) = anisotropicSquareKWMatrixPhase L x y omega u v d₂ d₁ := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWMatrixPhase_translation_invariant L x y omega u v t d₁ d₂

/--
[anisotropicSquareKWMatrixPhase_eq_blockCirculant](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWMatrixPhase_eq_blockCirculant_eq
  {L : Nat}
  {x y omega u v : Complex} :
-- imply
  anisotropicSquareKWMatrixPhase L x y omega u v = ons_blockCirculant2D L 4 (anisotropicSquareKWBlockPhase L x y omega u v) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWMatrixPhase_eq_blockCirculant L x y omega u v

/--
[anisotropicSquareKWBlockPhase_symbol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWBlockPhase_symbol_eq
  {L : Nat}
  [NeZero L]
  [Fact (1 < L)]
  {x y omega u v root : Complex}
  {j : ZMod L × ZMod L}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  ons_blockSymbol2D L 4 root (fun g ↦ (if g = 0 then (1 : Matrix (Fin 4) (Fin 4) Complex) else 0) - anisotropicSquareKWBlockPhase L x y omega u v g) j = anisotropicSquareKWSymbolMatrix x y omega (u * root ^ j.1.val) (v * root ^ j.2.val) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWBlockPhase_symbol L x y omega u v root homega hroot hu hv j

/--
[anisotropicSquareKWMatrixPhase_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWMatrixPhase_det_eq
  {L : Nat}
  [NeZero L]
  [Fact (1 < L)]
  {x y omega u v root : Complex}
-- given
  (homega : omega ^ 2 = Complex.I)
  (hroot : IsPrimitiveRoot root L)
  (hu : u ≠ 0)
  (hv : v ≠ 0) :
-- imply
  (1 - anisotropicSquareKWMatrixPhase L x y omega u v).det = ∏ j : ZMod L × ZMod L, ((1 + x ^ 2) * (1 + y ^ 2) - x * (1 - y ^ 2) * (u * root ^ j.1.val + (u * root ^ j.1.val)⁻¹) - y * (1 - x ^ 2) * (v * root ^ j.2.val + (v * root ^ j.2.val)⁻¹)) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWMatrixPhase_det L x y omega u v root homega hroot hu hv

/--
[anisotropicSquareKWMatrixPhase_det_eq_cosProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareKWMatrixPhase_det_eq_cosProduct_eq
  {L : Nat}
  [NeZero L]
  [Fact (1 < L)]
  {x y : Complex}
  {a b : Fin 2} :
-- imply
  (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det = ∏ j : ZMod L × ZMod L, ((1 + x ^ 2) * (1 + y ^ 2) - 2 * x * (1 - y ^ 2) * Real.cos (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) - 2 * y * (1 - x ^ 2) * Real.cos (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareKWMatrixPhase_det_eq_cosProduct L x y a b

/--
[anisotropicSquareEdgeWeight_port](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareEdgeWeight_port_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Complex}
  {d : ons_Dart L} :
-- imply
  anisotropicSquareEdgeWeight L x y (ons_portEdge L d) = squareTorusDirectionWeight x y d.2 := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareEdgeWeight_port L x y d

/--
[weightedPhase_anisotropicSquareEdgeWeight](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma weightedPhase_anisotropicSquareEdgeWeight_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y omega u v : Complex} :
-- imply
  ons_KWmatWeightedPhase L (anisotropicSquareEdgeWeight L x y) omega u v = anisotropicSquareKWMatrixPhase L x y omega u v := by
-- proof
  apply StatMech.FrontierA.weightedPhase_anisotropicSquareEdgeWeight L x y omega u v

/--
[anisotropicSquare_weightedSpin_sq_eq_det](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquare_weightedSpin_sq_eq_det_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Complex}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L x y) a b ^ 2 = (1 - anisotropicSquareKWMatrixPhase L x y ons_turnRoot (ons_spinPhase L a) (ons_spinPhase L b)).det := by
-- proof
  apply StatMech.FrontierA.anisotropicSquare_weightedSpin_sq_eq_det L x y a b

/--
[anisotropicSquare_weightedSpin_sq_eq_cosProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquare_weightedSpin_sq_eq_cosProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {x y : Complex}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L x y) a b ^ 2 = ∏ j : ZMod L × ZMod L, ((1 + x ^ 2) * (1 + y ^ 2) - 2 * x * (1 - y ^ 2) * Real.cos (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) - 2 * y * (1 - x ^ 2) * Real.cos (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L)) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquare_weightedSpin_sq_eq_cosProduct L x y a b

/--
[anisotropicSquareFourierFactor_eq_triangularHighTempSymbol](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquareFourierFactor_eq_triangularHighTempSymbol_eq
  {J₁ J₂ k q : Real} :
-- imply
  (1 + Real.tanh J₁ ^ 2) * (1 + Real.tanh J₂ ^ 2) - 2 * Real.tanh J₁ * (1 - Real.tanh J₂ ^ 2) * Real.cos k - 2 * Real.tanh J₂ * (1 - Real.tanh J₁ ^ 2) * Real.cos q = triangularIsingHighTempSymbol J₁ J₂ 0 k q := by
-- proof
  apply StatMech.FrontierA.anisotropicSquareFourierFactor_eq_triangularHighTempSymbol J₁ J₂ k q

/--
[anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {J₁ J₂ : Real}
  {a b : Fin 2} :
-- imply
  ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b ^ 2 = ∏ j : ZMod L × ZMod L, (triangularIsingHighTempSymbol J₁ J₂ 0 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquare_weightedSpin_tanh_sq_eq_triangularProduct L J₁ J₂ a b

/--
[anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct_eq
  {L : Nat}
  [Fact (2 < L)]
  {J₁ J₂ : Real}
  {a b : Fin 2} :
-- imply
  (((Real.cosh J₁ * Real.cosh J₂) ^ (L * L) : Real) * ons_weightedSpinCharacterSum L (anisotropicSquareEdgeWeight L (Real.tanh J₁) (Real.tanh J₂)) a b) ^ 2 = ∏ j : ZMod L × ZMod L, (triangularIsingSymbol J₁ J₂ 0 (2 * Real.pi * (j.1.val + (a.val : Real) / 2) / L) (2 * Real.pi * (j.2.val + (b.val : Real) / 2) / L) : Complex) := by
-- proof
  apply StatMech.FrontierA.anisotropicSquare_normalizedSpin_tanh_sq_eq_triangularProduct L J₁ J₂ a b

/--
[inhomogeneousIsingPartition_highTemperature](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma inhomogeneousIsingPartition_highTemperature_eq
  [Fintype V]
  [DecidableEq V]
  {G : SimpleGraph V}
  [DecidableRel G.Adj]
  {coupling : Sym2 V → Real} :
-- imply
  StatMech.Sharpness.ZJ G.edgeFinset coupling (fun _ ↦ 0) = (2 : Real) ^ Fintype.card V * (∏ edge ∈ G.edgeFinset, Real.cosh (coupling edge)) * inhomogeneousEvenSubgraphSum G (fun edge ↦ Real.tanh (coupling edge)) := by
-- proof
  apply StatMech.FrontierA.inhomogeneousIsingPartition_highTemperature G coupling

/--
[two_mul_inhomogeneousEvenSubgraphSum_eq_spin](https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/AnisotropicSquareTorusKacWard.lean)
-/
@[path]
private lemma two_mul_inhomogeneousEvenSubgraphSum_eq_spin_eq
  {L : Nat}
  [Fact (2 < L)]
  {weight : Sym2 (ZMod L × ZMod L) → Real} :
-- imply
  (2 : Complex) * inhomogeneousEvenSubgraphSum (onsTorusGraph L) weight = ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 1 + ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 1 + ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 1 0 - ons_weightedSpinCharacterSum L (fun edge ↦ (weight edge : Complex)) 0 0 := by
-- proof
  apply StatMech.FrontierA.two_mul_inhomogeneousEvenSubgraphSum_eq_spin L weight


-- created on 2026-10-23
