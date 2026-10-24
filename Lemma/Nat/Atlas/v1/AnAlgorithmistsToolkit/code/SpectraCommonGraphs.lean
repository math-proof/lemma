import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AnAlgorithmistsToolkit.code.SpectraCommonGraphs
open SpectraCommonGraphs GraphProductSpectrum
open Real SimpleGraph Matrix
open Matrix Finset


namespace SpectraCommonGraphs

/--
[cos_nat_mod_period](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma cos_nat_mod_period
  {k n : ℕ}
  {a : ℕ}
-- given
  (hn : (n : ℝ) ≠ 0) :
-- imply
  cos (2 * π * ↑k * ↑(a % n) / ↑n) = cos (2 * π * ↑k * ↑a / ↑n) := by
-- proof
  have hdiv : a = a % n + n * (a / n) := by have := Nat.div_add_mod a n; omega
  have heq : (↑a : ℝ) = ↑(a % n) + ↑n * ↑(a / n) := by exact_mod_cast hdiv
  conv_rhs => rw [heq]
  have heq2 : 2 * π * ↑k * (↑(a % n) + ↑n * ↑(a / n)) / ↑n
    = 2 * π * ↑k * ↑(a % n) / ↑n + ↑(a / n) * (↑k * (2 * π)) := by field_simp
  rw [heq2]
  exact ((cos_periodic.nat_mul k).nat_mul (a / n) _).symm

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[sin_nat_mod_period](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma sin_nat_mod_period
  {k n : ℕ}
  {a : ℕ}
-- given
  (hn : (n : ℝ) ≠ 0) :
-- imply
  sin (2 * π * ↑k * ↑(a % n) / ↑n) = sin (2 * π * ↑k * ↑a / ↑n) := by
-- proof
  have hdiv : a = a % n + n * (a / n) := by have := Nat.div_add_mod a n; omega
  have heq : (↑a : ℝ) = ↑(a % n) + ↑n * ↑(a / n) := by exact_mod_cast hdiv
  conv_rhs => rw [heq]
  have heq2 : 2 * π * ↑k * (↑(a % n) + ↑n * ↑(a / n)) / ↑n
    = 2 * π * ↑k * ↑(a % n) / ↑n + ↑(a / n) * (↑k * (2 * π)) := by field_simp
  rw [heq2]
  exact ((sin_periodic.nat_mul k).nat_mul (a / n) _).symm

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[cos_real_periodic_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma cos_real_periodic_add
  {k m : ℕ}
  {a : ℝ}
-- given
  (hm : (m : ℝ) ≠ 0) :
-- imply
  cos (2 * π * ↑k * (a + ↑m) / ↑m) = cos (2 * π * ↑k * a / ↑m) := by
-- proof
  have heq : 2 * π * (↑k : ℝ) * (a + ↑m) / ↑m
    = 2 * π * (↑k : ℝ) * a / ↑m + ↑k * (2 * π) := by field_simp
  rw [heq]; exact (cos_periodic.nat_mul k) _

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[sin_real_periodic_add](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma sin_real_periodic_add
  {k m : ℕ}
  {a : ℝ}
-- given
  (hm : (m : ℝ) ≠ 0) :
-- imply
  sin (2 * π * ↑k * (a + ↑m) / ↑m) = sin (2 * π * ↑k * a / ↑m) := by
-- proof
  have heq : 2 * π * (↑k : ℝ) * (a + ↑m) / ↑m
    = 2 * π * (↑k : ℝ) * a / ↑m + ↑k * (2 * π) := by field_simp
  rw [heq]; exact (sin_periodic.nat_mul k) _

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[fin_sub_one_ne_add_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma fin_sub_one_ne_add_one
  {n : ℕ}
  {v : Fin (n + 3)} :
-- imply
  v - 1 ≠ v + 1 := by
-- proof
  intro h
  have h2 : (-1 : Fin (n + 3)) = 1 := by
    have : (v - 1) - v = (v + 1) - v := congrArg (· - v) h; simpa using this
  exact absurd (Fin.val_eq_of_eq h2) (by simp [Fin.val_neg])

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[lapMatrix_mulVec_cosEigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma lapMatrix_mulVec_cosEigenvector
  {n : ℕ}
  {k : ℕ} :
-- imply
  (lapMatrix ℝ (ringGraph (n + 3))).mulVec (cosEigenvector (n + 3) k) = ringEigenvalue (n + 3) k • cosEigenvector (n + 3) k := by
-- proof
  ext ⟨u, hu⟩
  simp only [Pi.smul_apply, smul_eq_mul, ringGraph]
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (fin_sub_one_ne_add_one ⟨u, hu⟩)]
  simp only [cosEigenvector, ringEigenvalue]
  conv_lhs =>
    rw [show ((⟨u, hu⟩ - 1 : Fin (n + 3)).val : ℝ) = (((u + (n + 2)) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_sub]; ring_nf)]
    rw [show ((⟨u, hu⟩ + 1 : Fin (n + 3)).val : ℝ) = (((u + 1) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_add])]
  rw [cos_nat_mod_period k (n + 3) (by positivity) (u + (n + 2))]
  rw [cos_nat_mod_period k (n + 3) (by positivity) (u + 1)]
  rw [show (↑(u + (n + 2)) : ℝ) = ↑u - 1 + ↑(n + 3) from by push_cast; ring]
  rw [show (↑(u + 1) : ℝ) = (↑u : ℝ) + 1 from by push_cast; ring]
  rw [cos_real_periodic_add k (n + 3) (by positivity)]
  have hplus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) + 1) / ↑(n + 3)
    = 2 * π * ↑k * ↑u / ↑(n + 3) + 2 * π * ↑k / ↑(n + 3) := by ring
  have hminus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) - 1) / ↑(n + 3)
    = 2 * π * ↑k * ↑u / ↑(n + 3) - 2 * π * ↑k / ↑(n + 3) := by ring
  rw [hplus, hminus, cos_add, cos_sub]
  push_cast
  ring

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[lapMatrix_mulVec_sinEigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma lapMatrix_mulVec_sinEigenvector
  {n : ℕ}
  {k : ℕ} :
-- imply
  (lapMatrix ℝ (ringGraph (n + 3))).mulVec (sinEigenvector (n + 3) k) = ringEigenvalue (n + 3) k • sinEigenvector (n + 3) k := by
-- proof
  ext ⟨u, hu⟩
  simp only [Pi.smul_apply, smul_eq_mul, ringGraph]
  rw [lapMatrix_mulVec_apply, cycleGraph_degree_three_le, cycleGraph_neighborFinset,
    Finset.sum_pair (fin_sub_one_ne_add_one ⟨u, hu⟩)]
  simp only [sinEigenvector, ringEigenvalue]
  conv_lhs =>
    rw [show ((⟨u, hu⟩ - 1 : Fin (n + 3)).val : ℝ) = (((u + (n + 2)) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_sub]; ring_nf)]
    rw [show ((⟨u, hu⟩ + 1 : Fin (n + 3)).val : ℝ) = (((u + 1) % (n + 3) : ℕ) : ℝ) from
      congrArg (Nat.cast (R := ℝ)) (by simp [Fin.val_add])]
  rw [sin_nat_mod_period k (n + 3) (by positivity) (u + (n + 2))]
  rw [sin_nat_mod_period k (n + 3) (by positivity) (u + 1)]
  rw [show (↑(u + (n + 2)) : ℝ) = ↑u - 1 + ↑(n + 3) from by push_cast; ring]
  rw [show (↑(u + 1) : ℝ) = (↑u : ℝ) + 1 from by push_cast; ring]
  rw [sin_real_periodic_add k (n + 3) (by positivity)]
  have hplus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) + 1) / ↑(n + 3)
    = 2 * π * ↑k * ↑u / ↑(n + 3) + 2 * π * ↑k / ↑(n + 3) := by ring
  have hminus : 2 * π * (↑k : ℝ) * ((↑u : ℝ) - 1) / ↑(n + 3)
    = 2 * π * ↑k * ↑u / ↑(n + 3) - 2 * π * ↑k / ↑(n + 3) := by ring
  rw [hplus, hminus, sin_add, sin_sub]
  push_cast
  ring

end SpectraCommonGraphs

namespace SpectraCommonGraphs

/--
[ringGraph_lapMatrix_eigenvectors](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma ringGraph_lapMatrix_eigenvectors
  {n : ℕ}
  {k : ℕ} :
-- imply
  (lapMatrix ℝ (ringGraph (n + 3))).mulVec (cosEigenvector (n + 3) k) = ringEigenvalue (n + 3) k • cosEigenvector (n + 3) k ∧ (lapMatrix ℝ (ringGraph (n + 3))).mulVec (sinEigenvector (n + 3) k) = ringEigenvalue (n + 3) k • sinEigenvector (n + 3) k :=
-- proof
  ⟨lapMatrix_mulVec_cosEigenvector n k, lapMatrix_mulVec_sinEigenvector n k⟩
end
namespace GraphProductSpectrum
open Matrix Finset


namespace GraphProductSpectrum

/--
[kronecker_one_mulVec_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma kronecker_one_mulVec_tensor
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {A : Matrix V V ℝ}
  {v : V → ℝ}
  {w : W → ℝ} :
-- imply
  (kroneckerMap (· * ·) A (1 : Matrix W W ℝ)).mulVec (vecTensor v w) = vecTensor (A.mulVec v) w := by
-- proof
  ext ⟨a, b⟩
  simp only [vecTensor, mulVec, dotProduct, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul]
  congr 1; funext c
  have h : ∀ d : W, (A a c * if b = d then 1 else 0) * (v c * w d) =
    if b = d then A a c * v c * w b else 0 := by
    intro d; split_ifs with h; subst h; ring; ring
  simp_rw [h, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GraphProductSpectrum

namespace GraphProductSpectrum

/--
[one_kronecker_mulVec_tensor](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma one_kronecker_mulVec_tensor
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {B : Matrix W W ℝ}
  {v : V → ℝ}
  {w : W → ℝ} :
-- imply
  (kroneckerMap (· * ·) (1 : Matrix V V ℝ) B).mulVec (vecTensor v w) = vecTensor v (B.mulVec w) := by
-- proof
  ext ⟨a, b⟩
  simp only [vecTensor, mulVec, dotProduct, kroneckerMap_apply, one_apply,
    Fintype.sum_prod_type]
  trans (∑ c : V, if a = c then ∑ d : W, v a * (B b d * w d) else 0)
  · apply Finset.sum_congr rfl; intro c _
    split_ifs with h
    · subst h; apply Finset.sum_congr rfl; intro d _; ring
    · apply Finset.sum_eq_zero; intro d _; simp
  · simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.mul_sum]

end GraphProductSpectrum

namespace GraphProductSpectrum

/--
[kronecker_sum_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma kronecker_sum_eigenvector
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {A : Matrix V V ℝ}
  {B : Matrix W W ℝ}
  {v : V → ℝ}
  {w : W → ℝ}
  {eigA eigB : ℝ}
-- given
  (hv : A.mulVec v = eigA • v)
  (hw : B.mulVec w = eigB • w) :
-- imply
  (kroneckerMap (· * ·) A (1 : Matrix W W ℝ) + kroneckerMap (· * ·) (1 : Matrix V V ℝ) B).mulVec (vecTensor v w) = (eigA + eigB) • vecTensor v w := by
-- proof
  rw [add_mulVec, kronecker_one_mulVec_tensor, one_kronecker_mulVec_tensor, hv, hw]
  ext ⟨a, b⟩
  simp only [vecTensor, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

end GraphProductSpectrum

namespace GraphProductSpectrum

/--
[boxProd_degree_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma boxProd_degree_eq
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {v : V}
  {w : W} :
-- imply
  (G □ H).degree (v, w) = G.degree v + H.degree w := by
-- proof
  simp only [SimpleGraph.degree]
  rw [show (G □ H).neighborFinset (v, w) =
    ((G.neighborFinset v).map ⟨fun v' => (v', w), fun a b h => by simpa using h⟩) ∪
    ((H.neighborFinset w).map ⟨fun w' => (v, w'), fun a b h => by simpa using h⟩) from ?_]
  · rw [Finset.card_union_of_disjoint]
    · simp [Finset.card_map]
    · rw [Finset.disjoint_left]
      intro x hx1 hx2
      simp only [Finset.mem_map, Function.Embedding.coeFn_mk] at hx1 hx2
      obtain ⟨a, ha, rfl⟩ := hx1
      obtain ⟨b, _, heq⟩ := hx2
      have h1 : a = v := congr_arg Prod.fst heq.symm
      subst h1; rw [SimpleGraph.mem_neighborFinset] at ha; exact G.irrefl ha
  · ext ⟨v', w'⟩
    simp only [SimpleGraph.mem_neighborFinset, Finset.mem_union, Finset.mem_map,
      Function.Embedding.coeFn_mk, SimpleGraph.boxProd_adj]
    constructor
    · rintro (⟨hG, rfl⟩ | ⟨hH, rfl⟩)
      · left; exact ⟨v', hG, rfl⟩
      · right; exact ⟨w', hH, rfl⟩
    · rintro (⟨a, ha, h⟩ | ⟨b, hb, h⟩)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; left; exact ⟨ha, rfl⟩
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj h; right; exact ⟨hb, rfl⟩

end GraphProductSpectrum

namespace GraphProductSpectrum

/--
[lapMatrix_boxProd_eq_kronecker_sum](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma lapMatrix_boxProd_eq_kronecker_sum
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj] :
-- imply
  (G □ H).lapMatrix ℝ = kroneckerMap (· * ·) (G.lapMatrix ℝ) (1 : Matrix W W ℝ) + kroneckerMap (· * ·) (1 : Matrix V V ℝ) (H.lapMatrix ℝ) := by
-- proof
  ext ⟨v₁, w₁⟩ ⟨v₂, w₂⟩
  simp only [SimpleGraph.lapMatrix, SimpleGraph.degMatrix, SimpleGraph.adjMatrix,
    Matrix.sub_apply, Matrix.diagonal_apply, Matrix.of_apply,
    Matrix.add_apply, kroneckerMap_apply, Matrix.one_apply, Prod.mk.injEq]
  by_cases hv : v₁ = v₂ <;> by_cases hw : w₁ = w₂
  · subst hv; subst hw
    simp only [and_self, ite_true, mul_one, one_mul]
    have hadj : ¬(G □ H).Adj (v₁, w₁) (v₁, w₁) := (G □ H).irrefl
    simp only [hadj, G.irrefl, H.irrefl, ite_false, sub_zero]
    norm_cast; convert boxProd_degree_eq G H v₁ w₁ using 2
  · subst hv
    simp only [hw, and_false, ite_true, ite_false, mul_zero, zero_add, one_mul]
    have hadj : (G □ H).Adj (v₁, w₁) (v₁, w₂) ↔ H.Adj w₁ w₂ := by
      simp [SimpleGraph.boxProd_adj, hw]
    simp only [show (G □ H).Adj (v₁, w₁) (v₁, w₂) = H.Adj w₁ w₂ from propext hadj]
  · subst hw
    simp only [hv, and_true, ite_true, ite_false, mul_one, zero_mul, add_zero]
    have hadj : (G □ H).Adj (v₁, w₁) (v₂, w₁) ↔ G.Adj v₁ v₂ := by
      simp [SimpleGraph.boxProd_adj, hv]
    simp only [show (G □ H).Adj (v₁, w₁) (v₂, w₁) = G.Adj v₁ v₂ from propext hadj]
  · have hadj : ¬(G □ H).Adj (v₁, w₁) (v₂, w₂) := by
    rw [SimpleGraph.boxProd_adj]; push Not; exact ⟨fun _ => hw, fun _ => hv⟩
    simp only [hv, hw, and_false, ite_false, hadj, mul_zero, zero_mul, add_zero,
      sub_zero]

end GraphProductSpectrum

namespace GraphProductSpectrum

/--
[lapMatrix_boxProd_eigenvector](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AnAlgorithmistsToolkit/code/SpectraCommonGraphs.lean)
-/
@[path]
lemma lapMatrix_boxProd_eigenvector
  [Fintype V]
  [Fintype W]
  [DecidableEq V]
  [DecidableEq W]
  {G : SimpleGraph V}
  {H : SimpleGraph W}
  [DecidableRel G.Adj]
  [DecidableRel H.Adj]
  {v : V → ℝ}
  {w : W → ℝ}
  {eigG eigH : ℝ}
-- given
  (hv : (G.lapMatrix ℝ).mulVec v = eigG • v)
  (hw : (H.lapMatrix ℝ).mulVec w = eigH • w) :
-- imply
  ((G □ H).lapMatrix ℝ).mulVec (vecTensor v w) = (eigG + eigH) • vecTensor v w := by
-- proof
  rw [lapMatrix_boxProd_eq_kronecker_sum]
  exact kronecker_sum_eigenvector (G.lapMatrix ℝ) (H.lapMatrix ℝ) v w eigG eigH hv hw

end GraphProductSpectrum


-- created on 2026-10-23
