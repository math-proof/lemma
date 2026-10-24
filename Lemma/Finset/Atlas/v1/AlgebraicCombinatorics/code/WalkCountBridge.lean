import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicCombinatorics.code.WalkCountBridge
open WalkCountFormula NormalOrderCoeff Finset WalkCountBridge
open scoped Classical


namespace WalkCountBridge

/--
[toQ_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_zero
-- imply
  toQ (0 : YoungDiagram →₀ ℤ) = 0 := by
-- proof
ext; simp

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_add
  {f g : YoungDiagram →₀ ℤ} :
-- imply
  toQ (f + g) = toQ f + toQ g := by
-- proof
  ext; simp [Int.cast_add]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_sub
  {f g : YoungDiagram →₀ ℤ} :
-- imply
  toQ (f - g) = toQ f - toQ g := by
-- proof
  ext; simp [Int.cast_sub]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_smul](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_smul
  {c : ℤ}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  toQ (c • f) = (↑c : ℚ) • toQ f := by
-- proof
  ext; simp [smul_eq_mul, Int.cast_mul]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_liftU](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_liftU
  {f : YoungDiagram →₀ ℤ} :
-- imply
  toQ (liftU f) = liftU_Q (toQ f) := by
-- proof
  induction f using Finsupp.induction_linear with
  | zero => simp [toQ_zero]
  | add f g hf hg => simp only [map_add, toQ_add]; rw [hf, hg]
  | single a c => simp [toQ_smul]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_liftD](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_liftD
  {f : YoungDiagram →₀ ℤ} :
-- imply
  toQ (liftD f) = liftD_Q (toQ f) := by
-- proof
  induction f using Finsupp.induction_linear with
  | zero => simp [toQ_zero]
  | add f g hf hg => simp only [map_add, toQ_add]; rw [hf, hg]
  | single a c => simp [toQ_smul]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_emptyBasis](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_emptyBasis
-- imply
  toQ emptyBasis = emptyBasis_Q := by
-- proof
simp [emptyBasis, emptyBasis_Q]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_DplusU_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_DplusU_pow
  {n : ℕ}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  toQ (((liftD + liftU) ^ n) f) = ((liftD_Q + liftU_Q) ^ n) (toQ f) := by
-- proof
  induction n generalizing f with
  | zero =>
    simp only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply]
    rw [ih]
    congr 1
    show toQ ((liftD + liftU) f) = (liftD_Q + liftU_Q) (toQ f)
    simp only [LinearMap.add_apply, toQ_add, toQ_liftD, toQ_liftU]

end WalkCountBridge

namespace WalkCountBridge

/--
[toQ_liftU_pow](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma toQ_liftU_pow
  {n : ℕ}
  {f : YoungDiagram →₀ ℤ} :
-- imply
  toQ ((liftU ^ n) f) = (liftU_Q ^ n) (toQ f) := by
-- proof
  induction n generalizing f with
  | zero =>
    simp only [pow_zero, Module.End.one_eq_id, LinearMap.id_apply]
  | succ n ih =>
    rw [pow_succ, pow_succ, Module.End.mul_eq_comp, Module.End.mul_eq_comp,
      LinearMap.comp_apply, LinearMap.comp_apply, ih, toQ_liftU]

end WalkCountBridge

namespace WalkCountBridge

/--
[liftD_Q_comp_liftU_Q_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma liftD_Q_comp_liftU_Q_sub
  {f : YoungDiagram →₀ ℚ} :
-- imply
  liftD_Q (liftU_Q f) - liftU_Q (liftD_Q f) = f := by
-- proof
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add]; rw [add_sub_add_comm, hf, hg]
  | single a c =>
    have hZ := liftD_comp_liftU_sub (Finsupp.single a 1)
    simp only [liftU_single, one_smul, liftD_single, one_smul] at hZ
    simp only [liftU_Q_single, liftD_Q_single, map_smul, ← smul_sub]
    rw [← toQ_liftD (YoungDiagram.raisingOp a), ← toQ_liftU (YoungDiagram.loweringOp a)]
    rw [← toQ_sub, hZ]
    simp [Finsupp.smul_single', mul_one]

end WalkCountBridge

namespace WalkCountBridge

/--
[liftD_Q_mul_liftU_Q_sub](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma liftD_Q_mul_liftU_Q_sub
-- imply
  liftD_Q * liftU_Q - liftU_Q * liftD_Q = 1 := by
-- proof
  apply LinearMap.ext; intro f
  show liftD_Q (liftU_Q f) - liftU_Q (liftD_Q f) = f
  exact liftD_Q_comp_liftU_Q_sub f

end WalkCountBridge

namespace WalkCountBridge

/--
[liftD_Q_emptyBasis_Q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma liftD_Q_emptyBasis_Q
-- imply
  liftD_Q emptyBasis_Q = 0 := by
-- proof
  simp [emptyBasis_Q, loweringOp_bot, toQ_zero]

end WalkCountBridge

namespace WalkCountBridge

/--
[liftD_Q_pow_emptyBasis_Q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma liftD_Q_pow_emptyBasis_Q
  {j : ℕ}
-- given
  (hj : 0 < j) :
-- imply
  (liftD_Q ^ j) emptyBasis_Q = 0 := by
-- proof
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  induction k with
  | zero => simpa [pow_one] using liftD_Q_emptyBasis_Q
  | succ k _ =>
    rw [pow_succ, Module.End.mul_eq_comp, LinearMap.comp_apply,
      liftD_Q_emptyBasis_Q, map_zero]

end WalkCountBridge

namespace WalkCountBridge

/--
[pairsLE_filter_snd_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma pairsLE_filter_snd_zero
  {ℓ : ℕ} :
-- imply
  (pairsLE ℓ).filter (fun p => p.2 = 0) = (Finset.range (ℓ + 1)).map ⟨fun i => (i, 0), fun a b h => by simpa using h⟩ := by
-- proof
  ext ⟨a, b⟩
  simp only [Finset.mem_filter, mem_pairsLE, Finset.mem_map, Finset.mem_range,
    Function.Embedding.coeFn_mk]
  constructor
  · rintro ⟨hab, hb⟩; subst hb; exact ⟨a, by omega, rfl⟩
  · rintro ⟨i, hi, heq⟩; obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq; exact ⟨by omega, rfl⟩

end WalkCountBridge

namespace WalkCountBridge

/--
[normalOrder_term_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma normalOrder_term_apply
  {c : ℚ}
  {i j : ℕ} :
-- imply
  (algebraMap ℚ (Module.End ℚ (YoungDiagram →₀ ℚ)) c * (liftU_Q ^ i * liftD_Q ^ j)) emptyBasis_Q = c • ((liftU_Q ^ i) ((liftD_Q ^ j) emptyBasis_Q)) := by
-- proof
  show (algebraMap ℚ _ c * (liftU_Q ^ i * liftD_Q ^ j)) emptyBasis_Q = _
  rw [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, LinearMap.smul_apply, one_mul,
    Module.End.mul_eq_comp, LinearMap.comp_apply]

end WalkCountBridge

namespace WalkCountBridge

/--
[normalOrder_emptyBasis_Q](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma normalOrder_emptyBasis_Q
  {ell : ℕ} :
-- imply
  ((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q = ∑ i ∈ Finset.range (ell + 1), normalOrderCoeff i 0 ell • ((liftU_Q ^ i) emptyBasis_Q) := by
-- proof
  have hNO := NormalOrderCoeff.normalOrder_expansion liftD_Q liftU_Q
    liftD_Q_mul_liftU_Q_sub ell
  have heval : ((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q =
    ∑ p ∈ pairsLE ell,
      (algebraMap ℚ _ (normalOrderCoeff p.1 p.2 ell) *
        (liftU_Q ^ p.1 * liftD_Q ^ p.2)) emptyBasis_Q := by
    conv_lhs => rw [hNO]
    rw [LinearMap.sum_apply]
  rw [heval]
  simp_rw [normalOrder_term_apply]
  rw [← Finset.sum_filter_add_sum_filter_not (pairsLE ell) (fun p => p.2 = 0)]
  have hkill : ∑ p ∈ (pairsLE ell).filter (fun p => ¬p.2 = 0),
    normalOrderCoeff p.1 p.2 ell • (liftU_Q ^ p.1) ((liftD_Q ^ p.2) emptyBasis_Q) = 0 := by
    apply Finset.sum_eq_zero; intro p hp
    simp only [Finset.mem_filter] at hp
    rw [liftD_Q_pow_emptyBasis_Q (Nat.pos_of_ne_zero hp.2), map_zero, smul_zero]
  rw [hkill, add_zero]
  rw [pairsLE_filter_snd_zero, Finset.sum_map]
  simp only [Function.Embedding.coeFn_mk, pow_zero, Module.End.one_eq_id, LinearMap.id_apply]

end WalkCountBridge

namespace WalkCountBridge

/--
[DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
lemma DplusU_pow_emptyBasis_eq_sum_bijCoeff_iterU
  {ell : ℕ}
  {lam : YoungDiagram} :
-- imply
  ((((WalkCountFormula.liftD + WalkCountFormula.liftU) ^ ell) WalkCountFormula.emptyBasis) lam : ℚ) = ∑ i ∈ Finset.range (ell + 1), NormalOrderCoeff.bijCoeff i 0 ell * ((WalkCountFormula.iterU i WalkCountFormula.emptyBasis) lam : ℚ) := by
-- proof
  have hLHS : ((((liftD + liftU) ^ ell) emptyBasis) lam : ℚ) =
    (((liftD_Q + liftU_Q) ^ ell) emptyBasis_Q) lam := by
    rw [← toQ_apply]
    rw [toQ_DplusU_pow, toQ_emptyBasis]
  rw [hLHS, normalOrder_emptyBasis_Q]
  rw [Finset.sum_apply']
  congr 1; ext i
  simp only [Finsupp.smul_apply, smul_eq_mul]
  congr 1
  rw [show (liftU_Q ^ i) emptyBasis_Q = toQ ((liftU ^ i) emptyBasis) from by
    rw [toQ_liftU_pow, toQ_emptyBasis]]
  rw [toQ_apply]
  rfl
end WalkCountBridge


/--
[toQ_apply](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
private lemma toQ_apply_eq
  {f : YoungDiagram →₀ ℤ}
  {a : YoungDiagram} :
-- imply
  (toQ f) a = ↑(f a) := by
-- proof
  apply WalkCountBridge.toQ_apply f a

/--
[toQ_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
private lemma toQ_single_eq
  {a : YoungDiagram}
  {c : ℤ} :
-- imply
  toQ (Finsupp.single a c) = Finsupp.single a (↑c : ℚ) := by
-- proof
  apply WalkCountBridge.toQ_single a c

/--
[liftU_Q_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
private lemma liftU_Q_single_eq
  {a : YoungDiagram}
  {c : ℚ} :
-- imply
  liftU_Q (Finsupp.single a c) = c • toQ (YoungDiagram.raisingOp a) := by
-- proof
  apply WalkCountBridge.liftU_Q_single a c

/--
[liftD_Q_single](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicCombinatorics/code/WalkCountBridge.lean)
-/
@[path]
private lemma liftD_Q_single_eq
  {a : YoungDiagram}
  {c : ℚ} :
-- imply
  liftD_Q (Finsupp.single a c) = c • toQ (YoungDiagram.loweringOp a) := by
-- proof
  apply WalkCountBridge.liftD_Q_single a c


-- created on 2026-10-23
