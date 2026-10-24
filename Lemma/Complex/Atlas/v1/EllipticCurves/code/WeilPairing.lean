import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.EllipticCurves.code.WeilPairing
open WeierstrassCurve.Affine WeilPairing


namespace WeilPairing

/--
[functionEvalAtDivisor_mul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma functionEvalAtDivisor_mul
  [DecidableEq P]
  [CommGroup k]
  {f : P → k}
  {D₁ D₂ : P →₀ ℤ} :
-- imply
  functionEvalAtDivisor f (D₁ + D₂) = functionEvalAtDivisor f D₁ * functionEvalAtDivisor f D₂ := by
-- proof
  unfold functionEvalAtDivisor
  exact Finsupp.prod_add_index (fun a _ => zpow_zero (f a))
    (fun a _ b₁ b₂ => zpow_add (f a) b₁ b₂)

end WeilPairing

namespace WeilPairing

/--
[millerFunction_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunction_zero
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point} :
-- imply
  millerFunction W P 0 = fun _ => 1 :=
-- proof
  rfl

end WeilPairing

namespace WeilPairing

/--
[millerFunction_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunction_one
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point} :
-- imply
  millerFunction W P 1 = fun _ => 1 :=
-- proof
  rfl

end WeilPairing

namespace WeilPairing

/--
[millerFunctionNat_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunctionNat_succ
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point}
  {n : ℕ}
  {R : W.Point}
-- given
  (hn : 1 ≤ n) :
-- imply
  millerFunctionNat W P (n + 1) R = millerFunctionNat W P n R * lineFunctionG W P ((↑n : ℤ) • P) R := by
-- proof
  cases n with
  | zero => omega
  | succ m => simp only [millerFunctionNat]

end WeilPairing

namespace WeilPairing

/--
[millerFunction_neg](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunction_neg
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point}
  {n : ℕ}
  {R : W.Point}
-- given
  (hn : 0 < n) :
-- imply
  millerFunction W P (-(↑n : ℤ)) R = (millerFunction W P (↑n : ℤ) R * lineFunctionG W ((↑n : ℤ) • P) (-(↑n : ℤ) • P) R)⁻¹ := by
-- proof
  cases n with
  | zero => omega
  | succ m =>
    have hkey : -(↑(m + 1) : ℤ) = Int.negSucc m := by omega
    simp only [millerFunction, hkey]

end WeilPairing

namespace WeilPairing

/--
[millerFunction_divisor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunction_divisor
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point}
  {n : ℤ} :
-- imply
  millerFunctionDivisor W P n = n • Finsupp.single P 1 - (n - 1) • Finsupp.single (0 : W.Point) 1 - Finsupp.single ((n : ℤ) • P) 1 :=
-- proof
  rfl
/-- Additivity in the index (Lemma 23.24(ii)):
`f_{m+n,P} = f_{m,P} · f_{n,P} · G_{mP, nP}`. -/
section MillerDerived

end WeilPairing

namespace WeilPairing

/--
[millerFunction_divisor_deg_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerFunction_divisor_deg_zero
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {P : W.Point}
  {n : ℤ} :
-- imply
  (millerFunctionDivisor W P n).sum (fun _ k => k) = 0 := by
-- proof
  rw [millerFunction_divisor]
  simp [Finsupp.sum_sub_index, Finsupp.sum_single_index]
/-- Doubling formula for the Miller function:
`f_{2n,P} = f_{n,P}² · G_{nP, nP}`. Specialization of `millerFunction_add`. -/

end WeilPairing

namespace WeilPairing

/--
[functionEvalAtDivisor_zsmul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma functionEvalAtDivisor_zsmul
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  [DecidableEq P]
  [CommGroup k]
  {f : P → k}
  {n : ℤ}
  {D : P →₀ ℤ} :
-- imply
  functionEvalAtDivisor f (n • D) = functionEvalAtDivisor f D ^ n := by
-- proof
  change (n • D).support.prod (fun a => f a ^ ((n • D) a)) =
    (D.support.prod (fun a => f a ^ (D a))) ^ n
  rw [Finset.prod_subset (s₁ := (n • D).support) Finsupp.support_smul
    (fun x _ hx => by
      rw [Finsupp.notMem_support_iff.mp hx, zpow_zero]),
    ← Finset.prod_zpow]
  exact Finset.prod_congr rfl (fun p _ => by
    rw [Finsupp.smul_apply, smul_eq_mul, zpow_mul'])

end WeilPairing

namespace WeilPairing

/--
[weilPairingDiv_alternating](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma weilPairingDiv_alternating
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  [DecidableEq P]
  [CommGroup k]
  {f₁ f₂ : P → k}
  {D₁ D₂ : P →₀ ℤ} :
-- imply
  weilPairingDiv f₁ f₂ D₁ D₂ * weilPairingDiv f₂ f₁ D₂ D₁ = 1 := by
-- proof
  unfold weilPairingDiv
  group

end WeilPairing

namespace WeilPairing

/--
[weilPairingDiv_alternating_inv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma weilPairingDiv_alternating_inv
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  [DecidableEq P]
  [CommGroup k]
  {f₁ f₂ : P → k}
  {D₁ D₂ : P →₀ ℤ} :
-- imply
  weilPairingDiv f₁ f₂ D₁ D₂ = (weilPairingDiv f₂ f₁ D₂ D₁)⁻¹ :=
-- proof
  mul_eq_one_iff_eq_inv.mp (weilPairingDiv_alternating f₁ f₂ D₁ D₂)

end WeilPairing

namespace WeilPairing

/--
[pow_div_mem_rootsOfUnity](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma pow_div_mem_rootsOfUnity
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  [CommGroup G]
  [Fintype G]
  {u : G}
  {n : ℕ}
-- given
  (hn : n ∣ Fintype.card G) :
-- imply
  (u ^ (Fintype.card G / n)) ^ n = 1 := by
-- proof
  rw [← pow_mul, Nat.div_mul_cancel hn, pow_card_eq_one]
/-- The (modified) Tate pairing `t_n : E[n] × E[n] → μ_n` (Definition 23.34), defined on a
finite field `F` with embedding degree `k`: `t_n(P, Q) := (f_{n,P}(Q) / f_{n,P}(0))^{(|F|^k - 1)/n}`.
-/
section Lemma2333
open WeierstrassCurve.Affine
variable {F : Type*} [Field F] [DecidableEq F] [Fintype F]
/-- The Frobenius endomorphism `π_E : E(F̄) → E(F̄)` on a finite-field elliptic curve, packaged
as an additive group homomorphism on `W.Point`. -/
end Lemma2333
section Corollary_23_25

end WeilPairing

namespace WeilPairing

/--
[millerEvalCost_le_log](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/EllipticCurves/code/WeilPairing.lean)
-/
@[path]
lemma millerEvalCost_le_log
  [Field F₀]
  [DecidableEq F₀]
  [Field F]
  [DecidableEq F]
  [Field F]
  [DecidableEq F]
  {W : WeierstrassCurve.Affine F}
  {n : ℕ} :
-- imply
  millerEvalCost n ≤ 2 * Nat.log 2 n + 2 := by
-- proof
  induction n using Nat.strongRecOn with
  | _ n ih =>
    match n with
    | 0 => simp [millerEvalCost]
    | 1 => simp [millerEvalCost]
    | n + 2 =>
      simp only [millerEvalCost]
      have hm : (n + 2) / 2 < n + 2 := Nat.div_lt_self (by omega) (by omega)
      have h_ih := ih ((n + 2) / 2) hm
      have h_log : Nat.log 2 (n + 2) = Nat.log 2 ((n + 2) / 2) + 1 :=
        Nat.log_of_one_lt_of_le (by omega) (by omega)
      split_ifs with h
      ·
        omega
      ·
        omega
section Corollary_23_30
/-- Galois-equivariance refinement (Corollary 23.30): if `E[n] ⊆ E(L)` then every `n`-th root
of unity in `L` actually lies in (the image of) `K`. -/
end Corollary_23_30
section Corollary_23_31

end WeilPairing


-- created on 2026-10-23
