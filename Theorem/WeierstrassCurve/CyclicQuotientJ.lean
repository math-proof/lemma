module

public import Mathlib
public import Theorem.WeierstrassCurve.Velu
public import Theorem.WeierstrassCurve.VeluOrderTwo
public import Theorem.WeierstrassCurve.VeluPointMap2
public import Theorem.WeierstrassCurve.OddOrderSummingSet
public import Abbrev.WeierstrassCurve_CyclicQuotientJ

public noncomputable section

set_option autoImplicit false

noncomputable section

namespace WeierstrassCurve

section XData

variable {R : Type*} [CommRing R] (V : WeierstrassCurve R)


public theorem xVeluT_eq_veluT (x y : R) : V.xVeluT x = V.veluT x y := by
  rw [xVeluT, veluT_eq]


public theorem xVeluU_eq_veluU {x y : R} (h : V.toAffine.Equation x y) : V.xVeluU x = V.veluU x y := by
  rw [V.veluU_eq_Ψ₂Sq_eval h, xVeluU, Ψ₂Sq]
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X]


public theorem xVeluW_eq_veluW {x y : R} (h : V.toAffine.Equation x y) : V.xVeluW x = V.veluW x y := by
  rw [xVeluW, veluW, V.xVeluU_eq_veluU h, V.xVeluT_eq_veluT x y]

end XData

section Field

variable {L : Type*} [Field L]


public theorem absSum_of_finite {X : Set L} (hX : X.Finite) (g : L → L) :
    absSum X g = ∑ x ∈ hX.toFinset, g x := by
  rw [absSum, if_pos hX, finsum_mem_eq_finite_toFinset_sum g hX]


public theorem absSum_of_infinite {X : Set L} (hX : X.Infinite) (g : L → L) : absSum X g = 0 := by
  rw [absSum, if_neg hX]


@[simp] public theorem xVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₁ = V.a₁ := rfl

@[simp] public theorem xVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₂ = V.a₂ := rfl

@[simp] public theorem xVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.xVeluCurve X).a₃ = V.a₃ := rfl

public theorem xVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluT := rfl

public theorem xVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.xVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluT - 7 * absSum X V.xVeluW := rfl


@[simp] public theorem twoVeluCurve_a₁ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₁ = V.a₁ := rfl

@[simp] public theorem twoVeluCurve_a₂ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₂ = V.a₂ := rfl

@[simp] public theorem twoVeluCurve_a₃ (V : WeierstrassCurve L) (X : Set L) : (V.twoVeluCurve X).a₃ = V.a₃ := rfl

public theorem twoVeluCurve_a₄ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₄ = V.a₄ - 5 * absSum X V.xVeluG := rfl

public theorem twoVeluCurve_a₆ (V : WeierstrassCurve L) (X : Set L) :
    (V.twoVeluCurve X).a₆ = V.a₆ - V.b₂ * absSum X V.xVeluG - 7 * absSum X fun x => x * V.xVeluG x :=
  rfl

variable [DecidableEq L]


public theorem stepCurve_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.stepCurve H 2 = V.twoVeluCurve (V.kernelXSet H 2) :=
  if_pos rfl


public theorem stepCurve_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) : V.stepCurve H ℓ = V.xVeluCurve (V.kernelXSet H ℓ) :=
  if_neg hℓ


public theorem stepX_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (x : L) :
    V.stepX H 2 x = V.twoVeluX (V.kernelXSet H 2) x :=
  if_pos rfl


public theorem stepX_of_ne_two (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) {ℓ : ℕ}
    (hℓ : ℓ ≠ 2) (x : L) : V.stepX H ℓ x = V.xVeluX (V.kernelXSet H ℓ) x :=
  if_neg hℓ


public theorem cqjIterate_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cqjIterate H N = cqjStep^[N.primeFactorsList.length] ⟨⟨V, H⟩, N⟩ := rfl


public theorem cyclicQuotientCurve_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    (N : ℕ) : V.cyclicQuotientCurve H N = (V.cqjIterate H N).1.1 := rfl


public theorem cyclicQuotientJ_def (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ) :
    V.cyclicQuotientJ H N =
      (V.cyclicQuotientCurve H N).c₄ ^ 3 / (V.cyclicQuotientCurve H N).Δ := rfl


public theorem cqjStep_apply (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (n : ℕ) :
    cqjStep ⟨⟨V, H⟩, n⟩ =
      ⟨⟨V.stepCurve H n.minFac, V.stepSubgroup H n.minFac⟩, n / n.minFac⟩ := rfl


public theorem cqjIterate_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cqjIterate H 1 = ⟨⟨V, H⟩, 1⟩ := by
  simp [cqjIterate, Nat.primeFactorsList_one]


public theorem cyclicQuotientCurve_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientCurve H 1 = V := by
  rw [cyclicQuotientCurve_def, cqjIterate_one]


public theorem cyclicQuotientJ_one (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) :
    V.cyclicQuotientJ H 1 = V.c₄ ^ 3 / V.Δ := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_one]


public theorem length_primeFactorsList_eq_succ {N : ℕ} (hN : 2 ≤ N) :
    N.primeFactorsList.length = (N / N.minFac).primeFactorsList.length + 1 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = k + 2 := ⟨N - 2, by omega⟩
  rw [Nat.primeFactorsList, List.length_cons]


public theorem cqjIterate_eq_of_two_le (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point)
    {N : ℕ} (hN : 2 ≤ N) :
    V.cqjIterate H N =
      (V.stepCurve H N.minFac).cqjIterate (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cqjIterate, length_primeFactorsList_eq_succ hN, Function.iterate_succ_apply]
  rfl


public theorem cyclicQuotientCurve_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientCurve H N =
      (V.stepCurve H N.minFac).cyclicQuotientCurve (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientCurve_def, cqjIterate_eq_of_two_le V H hN, cyclicQuotientCurve_def]


public theorem cyclicQuotientJ_eq_of_two_le (V : WeierstrassCurve L)
    (H : AddSubgroup V.toAffine.Point) {N : ℕ} (hN : 2 ≤ N) :
    V.cyclicQuotientJ H N =
      (V.stepCurve H N.minFac).cyclicQuotientJ (V.stepSubgroup H N.minFac) (N / N.minFac) := by
  rw [cyclicQuotientJ_def, cyclicQuotientCurve_eq_of_two_le V H hN, cyclicQuotientJ_def]


public theorem cyclicQuotientJ_eq_j (V : WeierstrassCurve L) (H : AddSubgroup V.toAffine.Point) (N : ℕ)
    [(V.cyclicQuotientCurve H N).IsElliptic] :
    V.cyclicQuotientJ H N = (V.cyclicQuotientCurve H N).j := by
  rw [cyclicQuotientJ_def, WeierstrassCurve.j, div_eq_mul_inv, mul_comm, Units.val_inv_eq_inv_val,
    WeierstrassCurve.coe_Δ']

end Field

end WeierstrassCurve

end
