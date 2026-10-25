/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/StatisticalMechanics/Code/FrontierA/IsingCriticalOddPrismLayerCoordinates.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Theorem.StatisticalMechanics.Code.FrontierA.IsingCriticalUnequalBridgeGeometry.Part3
import Theorem.StatisticalMechanics.Code.Ising.GHSLebowitz.Part11
import Theorem.StatisticalMechanics.Code.Ising.IsingFKGLayer
import Theorem.StatisticalMechanics.Code.Ising.RectangularPrismTransfer.Part7
import Def.StatisticalMechanics.Code.FrontierA.IsingCriticalOddPrismLayerCoordinates.Part20


namespace StatMech.FrontierA

open StatMech StatMech.Ising StatMech.Sharpness

open Matrix

open scoped BigOperators

noncomputable section

theorem oddPrismThreeLayerMarkedRawMoment_swap
    (beta : Real) (n : Nat) (a b : Real) (F : Real -> Real -> Real) :
    oddPrismThreeLayerMarkedRawMoment beta n a b F =
      oddPrismThreeLayerMarkedRawMoment beta n b a (fun x y => F y x) := by
  unfold oddPrismThreeLayerMarkedRawMoment
  apply Finset.sum_congr rfl
  intro s _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  apply Finset.sum_congr rfl
  intro v _
  ring

theorem oddPrismTransferBridgeRawMoment_eq_finiteExpMoment
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawMoment beta n r =
      finiteExpMoment (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawMoment finiteExpMoment
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  rfl

theorem oddPrismTransferBridgeRawFirst_eq_finiteExpFirst
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawFirst beta n r =
      finiteExpFirst (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawFirst finiteExpFirst
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  ring

theorem oddPrismTransferBridgeRawSecond_eq_finiteExpSecond
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeRawSecond beta n r =
      finiteExpSecond (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeRawSecond finiteExpSecond
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro q _
  unfold oddPrismTransferPairBaseWeight oddPrismTransferPairInteraction
    oddPrismPureSeamKernel
  ring

theorem oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp
    (beta : Real) (n : Nat) (r : Real) :
    oddPrismTransferBridgeVarianceSkewNumerator beta n r =
      finiteExpVarianceSkew (oddPrismTransferPairBaseWeight beta n)
        (oddPrismTransferPairInteraction n) r := by
  unfold oddPrismTransferBridgeVarianceSkewNumerator
    oddPrismTransferBridgeVarianceNumerator finiteExpVarianceSkew
  rw [oddPrismTransferBridgeRawMoment_eq_finiteExpMoment,
    oddPrismTransferBridgeRawMoment_eq_finiteExpMoment,
    oddPrismTransferBridgeRawFirst_eq_finiteExpFirst,
    oddPrismTransferBridgeRawFirst_eq_finiteExpFirst,
    oddPrismTransferBridgeRawSecond_eq_finiteExpSecond,
    oddPrismTransferBridgeRawSecond_eq_finiteExpSecond]


theorem two_mul_oddPrismTransferBridgeVarianceSkewNumerator_eq_fourStateSum
    (beta : Real) (n : Nat) (r : Real) :
    2 * oddPrismTransferBridgeVarianceSkewNumerator beta n r =
      let w := oddPrismTransferPairBaseWeight beta n
      let I := oddPrismTransferPairInteraction n
      ∑ x, ∑ y, ∑ z, ∑ q,
        w x * w y * w z * w q * (I x - I y) ^ 2 *
          (Real.exp (r * (I x + I y - I z - I q)) -
            Real.exp (-r * (I x + I y - I z - I q))) := by
  rw [oddPrismTransferBridgeVarianceSkewNumerator_eq_finiteExp]
  exact two_mul_finiteExpVarianceSkew_eq_fourStateSum
    (oddPrismTransferPairBaseWeight beta n)
    (oddPrismTransferPairInteraction n) r


theorem finiteMarginal_logSupermodular
    {A B : Type*} [Fintype A] [Fintype B]
    [DistribLattice A] [DistribLattice B]
    (F : A × B -> Real) (hF : 0 <= F)
    (hlog : ∀ x y, F x * F y <= F (x ⊓ y) * F (x ⊔ y))
    (x y : A) :
    (∑ b, F (x, b)) * (∑ b, F (y, b)) <=
      (∑ b, F (x ⊓ y, b)) * (∑ b, F (x ⊔ y, b)) := by
  apply four_functions_theorem_univ
  · exact fun b => hF (x, b)
  · exact fun b => hF (y, b)
  · exact fun b => hF (x ⊓ y, b)
  · exact fun b => hF (x ⊔ y, b)
  · intro b c
    simpa only [Prod.inf_def, Prod.sup_def] using
      (hlog (x, b) (y, c))


theorem rectangularLayerInternalInteraction_supermodular
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    rectangularLayerInternalInteraction s +
        rectangularLayerInternalInteraction t <=
      rectangularLayerInternalInteraction (s ⊔ t) +
        rectangularLayerInternalInteraction (s ⊓ t) := by
  have hx :
      (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin s (⟨x.val, by omega⟩, y) *
            spin s (⟨x.val + 1, by omega⟩, y)) +
        (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin t (⟨x.val, by omega⟩, y) *
            spin t (⟨x.val + 1, by omega⟩, y)) <=
      (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin (s ⊔ t) (⟨x.val, by omega⟩, y) *
            spin (s ⊔ t) (⟨x.val + 1, by omega⟩, y)) +
        (∑ x : Fin (m - 1), ∑ y : Fin n,
          spin (s ⊓ t) (⟨x.val, by omega⟩, y) *
            spin (s ⊓ t) (⟨x.val + 1, by omega⟩, y)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    simpa only [bond_mk] using
      (ifk_bond_supermodular s t
        s((⟨x.val, by omega⟩, y), (⟨x.val + 1, by omega⟩, y)))
  have hy :
      (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin s (x, ⟨y.val, by omega⟩) *
            spin s (x, ⟨y.val + 1, by omega⟩)) +
        (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin t (x, ⟨y.val, by omega⟩) *
            spin t (x, ⟨y.val + 1, by omega⟩)) <=
      (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin (s ⊔ t) (x, ⟨y.val, by omega⟩) *
            spin (s ⊔ t) (x, ⟨y.val + 1, by omega⟩)) +
        (∑ x : Fin m, ∑ y : Fin (n - 1),
          spin (s ⊓ t) (x, ⟨y.val, by omega⟩) *
            spin (s ⊓ t) (x, ⟨y.val + 1, by omega⟩)) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro x _
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro y _
    simpa only [bond_mk] using
      (ifk_bond_supermodular s t
        s((x, ⟨y.val, by omega⟩), (x, ⟨y.val + 1, by omega⟩)))
  unfold rectangularLayerInternalInteraction
  linarith


theorem rectangularLayerBoundaryInteraction_modular
    {m n : Nat} (s t : RectangularLayerConfig m n) :
    (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin s p) +
        (∑ p : Fin m × Fin n, rectangularLayerBoundaryDegree p * spin t p) =
      (∑ p : Fin m × Fin n,
        rectangularLayerBoundaryDegree p * spin (s ⊔ t) p) +
        ∑ p : Fin m × Fin n,
          rectangularLayerBoundaryDegree p * spin (s ⊓ t) p := by
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  have hp := ifk_spin_modular s t p
  nlinarith


theorem rectangularLayerBoltzmannInteraction_supermodular
    {beta : Real} (hbeta : 0 <= beta) {m n : Nat}
    (s t : RectangularLayerConfig m n) :
    rectangularLayerBoltzmannInteraction 1 beta s +
        rectangularLayerBoltzmannInteraction 1 beta t <=
      rectangularLayerBoltzmannInteraction 1 beta (s ⊔ t) +
        rectangularLayerBoltzmannInteraction 1 beta (s ⊓ t) := by
  have hi := rectangularLayerInternalInteraction_supermodular s t
  have hb := rectangularLayerBoundaryInteraction_modular s t
  unfold rectangularLayerBoltzmannInteraction
  norm_num
  nlinarith [mul_nonneg hbeta (sub_nonneg.mpr hi)]


theorem oddPrismLayerHalfWeight_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerHalfWeight beta n s * oddPrismLayerHalfWeight beta n t <=
      oddPrismLayerHalfWeight beta n (s ⊔ t) *
        oddPrismLayerHalfWeight beta n (s ⊓ t) := by
  unfold oddPrismLayerHalfWeight
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := rectangularLayerBoltzmannInteraction_supermodular hbeta s t
  linarith


theorem oddPrismLayerSeamInteraction_pair_supermodular
    (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismLayerSeamInteraction n s v +
        oddPrismLayerSeamInteraction n t w <=
      oddPrismLayerSeamInteraction n (s ⊔ t) (v ⊔ w) +
        oddPrismLayerSeamInteraction n (s ⊓ t) (v ⊓ w) := by
  let a : ConfigSpace
      (Sum (Fin (2 * n + 1) × Fin (2 * n + 1))
        (Fin (2 * n + 1) × Fin (2 * n + 1))) := Sum.elim s v
  let b : ConfigSpace
      (Sum (Fin (2 * n + 1) × Fin (2 * n + 1))
        (Fin (2 * n + 1) × Fin (2 * n + 1))) := Sum.elim t w
  unfold oddPrismLayerSeamInteraction
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro p _
  have hp := ifk_bond_supermodular a b s(Sum.inl p, Sum.inr p)
  simpa only [bond_mk, a, b] using hp


theorem oddPrismPureSeamKernel_pair_logSupermodular
    {r : Real} (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismPureSeamKernel r n s v * oddPrismPureSeamKernel r n t w <=
      oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
        oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) := by
  unfold oddPrismPureSeamKernel
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have h := oddPrismLayerSeamInteraction_pair_supermodular n s t v w
  nlinarith [mul_nonneg hr (sub_nonneg.mpr h)]


theorem oddPrismTiltedSeamTransfer_pair_logSupermodular
    {beta r : Real} (hbeta : 0 <= beta) (hr : 0 <= r) (n : Nat)
    (s t v w : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    oddPrismTiltedSeamTransfer beta n r s v *
        oddPrismTiltedSeamTransfer beta n r t w <=
      oddPrismTiltedSeamTransfer beta n r (s ⊔ t) (v ⊔ w) *
        oddPrismTiltedSeamTransfer beta n r (s ⊓ t) (v ⊓ w) := by
  have hs := oddPrismLayerHalfWeight_logSupermodular hbeta n s t
  have hv := oddPrismLayerHalfWeight_logSupermodular hbeta n v w
  have hk := oddPrismPureSeamKernel_pair_logSupermodular hr n s t v w
  have hs0 (a : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismLayerHalfWeight beta n a :=
    (oddPrismLayerHalfWeight_pos beta n a).le
  have hk0 (a b : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
      0 <= oddPrismPureSeamKernel r n a b :=
    (oddPrismPureSeamKernel_pos r n a b).le
  unfold oddPrismTiltedSeamTransfer
  calc
    (oddPrismLayerHalfWeight beta n s * oddPrismPureSeamKernel r n s v *
          oddPrismLayerHalfWeight beta n v) *
        (oddPrismLayerHalfWeight beta n t * oddPrismPureSeamKernel r n t w *
          oddPrismLayerHalfWeight beta n w) =
      (oddPrismLayerHalfWeight beta n s * oddPrismLayerHalfWeight beta n t) *
        (oddPrismPureSeamKernel r n s v * oddPrismPureSeamKernel r n t w) *
        (oddPrismLayerHalfWeight beta n v * oddPrismLayerHalfWeight beta n w) := by ring
    _ <=
      (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismLayerHalfWeight beta n (s ⊓ t)) *
        (oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w)) *
        (oddPrismLayerHalfWeight beta n (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊓ w)) := by
            gcongr
            · exact mul_nonneg (hs0 v) (hs0 w)
            · exact mul_nonneg
                (mul_nonneg (hs0 (s ⊔ t)) (hs0 (s ⊓ t)))
                (mul_nonneg (hk0 (s ⊔ t) (v ⊔ w))
                  (hk0 (s ⊓ t) (v ⊓ w)))
            · exact mul_nonneg (hk0 s v) (hk0 t w)
            · exact mul_nonneg (hs0 (s ⊔ t)) (hs0 (s ⊓ t))
    _ =
      (oddPrismLayerHalfWeight beta n (s ⊔ t) *
          oddPrismPureSeamKernel r n (s ⊔ t) (v ⊔ w) *
          oddPrismLayerHalfWeight beta n (v ⊔ w)) *
        (oddPrismLayerHalfWeight beta n (s ⊓ t) *
          oddPrismPureSeamKernel r n (s ⊓ t) (v ⊓ w) *
          oddPrismLayerHalfWeight beta n (v ⊓ w)) := by ring


theorem rectangularLayerFaceBoundary_modular
    (beta : Real) {m n : Nat} (s t : RectangularLayerConfig m n) :
    rectangularLayerFaceBoundary 1 beta s +
        rectangularLayerFaceBoundary 1 beta t =
      rectangularLayerFaceBoundary 1 beta (s ⊔ t) +
        rectangularLayerFaceBoundary 1 beta (s ⊓ t) := by
  unfold rectangularLayerFaceBoundary
  norm_num
  rw [← mul_add, ← mul_add]
  congr 1
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  exact ifk_spin_modular s t p


theorem rectangularPrismTransferBoundaryVector_logSupermodular
    {beta : Real} (hbeta : 0 <= beta) (n : Nat)
    (s t : RectangularLayerConfig (2 * n + 1) (2 * n + 1)) :
    rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) s *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) t <=
      rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊓ t) *
        rectangularPrismTransferBoundaryVector 1 beta
          (2 * n + 1) (2 * n + 1) (s ⊔ t) := by
  unfold rectangularPrismTransferBoundaryVector
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hi := rectangularLayerBoltzmannInteraction_supermodular hbeta s t
  have hf := rectangularLayerFaceBoundary_modular beta s t
  linarith


theorem transferTailPathWeight_logSupermodular
    {E : Type*} [Fintype E] [DistribLattice E]
    (A : Matrix E E Real) (a : E -> Real)
    (ha0 : 0 <= a) (hA0 : ∀ x y, 0 <= A x y)
    (ha : ∀ x y, a x * a y <= a (x ⊓ y) * a (x ⊔ y))
    (hA : ∀ x y u v,
      A x u * A y v <= A (x ⊓ y) (u ⊓ v) * A (x ⊔ y) (u ⊔ v))
    (k : Nat) (q r : Fin (k + 1) -> E) :
    transferTailPathWeight A a k q * transferTailPathWeight A a k r <=
      transferTailPathWeight A a k (q ⊓ r) *
        transferTailPathWeight A a k (q ⊔ r) := by
  have hp :
      (∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
          (∏ j : Fin k, A (r j.castSucc) (r j.succ)) <=
        (∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ) := by
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    apply Finset.prod_le_prod
    · intro j _
      exact mul_nonneg (hA0 _ _) (hA0 _ _)
    · intro j _
      simpa only [Pi.inf_apply, Pi.sup_apply] using
        hA (q j.castSucc) (r j.castSucc) (q j.succ) (r j.succ)
  unfold transferTailPathWeight
  calc
    (a (q 0) * ∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
        (a (r 0) * ∏ j : Fin k, A (r j.castSucc) (r j.succ)) =
      (a (q 0) * a (r 0)) *
        ((∏ j : Fin k, A (q j.castSucc) (q j.succ)) *
          ∏ j : Fin k, A (r j.castSucc) (r j.succ)) := by ring
    _ <= (a ((q ⊓ r) 0) * a ((q ⊔ r) 0)) *
        ((∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by
      apply mul_le_mul
      · simpa only [Pi.inf_apply, Pi.sup_apply] using ha (q 0) (r 0)
      · exact hp
      · exact mul_nonneg
          (Finset.prod_nonneg fun j _ => hA0 _ _)
          (Finset.prod_nonneg fun j _ => hA0 _ _)
      · exact mul_nonneg (ha0 _) (ha0 _)
    _ =
      (a ((q ⊓ r) 0) *
          ∏ j : Fin k, A ((q ⊓ r) j.castSucc) ((q ⊓ r) j.succ)) *
        (a ((q ⊔ r) 0) *
          ∏ j : Fin k, A ((q ⊔ r) j.castSucc) ((q ⊔ r) j.succ)) := by ring


theorem sum_transferTailPathWeight_fixed_endpoint
    {E : Type*} [Fintype E] [DecidableEq E]
    (A : Matrix E E Real) (hA : A.IsHermitian) (a : E -> Real)
    (k : Nat) (s : E) :
    (∑ q : Fin k -> E,
      transferTailPathWeight A a k (Fin.snoc q s)) = ((A ^ k) *ᵥ a) s := by
  let f : E -> Real := fun t => if t = s then 1 else 0
  have h := sum_transferTailPathWeight_mul_endpoint A hA a f k
  rw [← Equiv.sum_comp (Fin.snocEquiv fun _ : Fin (k + 1) => E)] at h
  rw [Fintype.sum_prod_type] at h
  simpa [Fin.snocEquiv, f] using h


end
end StatMech.FrontierA
