import Mathlib
import sympy.Basic
import Def.v1.Atlas.DifferentialAnalysis.code.SobolevDerivatives
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory
open scoped SchwartzMap FourierTransform


namespace SobolevSpace

/--
[iteratedPartialDerivDistrib_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma iteratedPartialDerivDistrib_eq
  {n : ℕ}
  {n : ℕ}
  {i : Fin n}
  {k : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iteratedPartialDerivDistrib n i k u = FourierInversion.iterDistribDerivCoord i k u := by
-- proof
  simp only [iteratedPartialDerivDistrib, FourierInversion.iterDistribDerivCoord,
    distribDerivCLM, LineDeriv.lineDerivOpCLM_apply]

end SobolevSpace

namespace SobolevSpace

/--
[iteratedDistribDeriv_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma iteratedDistribDeriv_eq
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iteratedDistribDeriv n α u = FourierInversion.iterDistribDeriv α u := by
-- proof
  unfold iteratedDistribDeriv FourierInversion.iterDistribDeriv
  induction (List.finRange n) generalizing u with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons]
    rw [iteratedPartialDerivDistrib_eq]; exact congrArg _ (ih _)

end SobolevSpace

namespace SobolevSpace

/--
[abs_inner_single_le_japaneseBracket](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma abs_inner_single_le_japaneseBracket
  {n : ℕ}
  {n : ℕ}
  {j : Fin n}
  {ξ : EuclideanSpace ℝ (Fin n)} :
-- imply
  |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))| ≤ japaneseBracket n ξ := by
-- proof
  have : |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))| ≤ ‖ξ‖ := by
    calc |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))|
      ≤ ‖ξ‖ * ‖EuclideanSpace.single j (1 : ℝ)‖ := abs_real_inner_le_norm _ _
      _ = ‖ξ‖ := by rw [PiLp.norm_single, norm_one, mul_one]
  calc |@inner ℝ _ _ ξ (EuclideanSpace.single j (1 : ℝ))|
    ≤ ‖ξ‖ := this
    _ ≤ Real.sqrt (1 + ‖ξ‖ ^ 2) := by
      rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
      nlinarith [sq_nonneg ‖ξ‖]
    _ = japaneseBracket n ξ := rfl

end SobolevSpace

namespace SobolevSpace

/--
[norm_two_pi_I](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma norm_two_pi_I
  {n : ℕ} :
-- imply
  ‖(2 * ↑Real.pi * Complex.I : ℂ)‖ = 2 * Real.pi := by
-- proof
  rw [show (2 : ℂ) * ↑Real.pi * Complex.I = ↑(2 * Real.pi) * Complex.I by push_cast; ring]
  rw [Complex.norm_mul, Complex.norm_real, Complex.norm_I, mul_one,
    Real.norm_of_nonneg (by positivity)]
set_option maxHeartbeats 400000 in

end SobolevSpace

namespace SobolevSpace

/--
[memHs_distribDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma memHs_distribDeriv
  {n : ℕ}
  {n : ℕ}
  {s : ℝ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : MemHs n s u) :
-- imply
  MemHs n (s - 1) (distribDerivCLM (F := ℂ) (EuclideanSpace.single j (1 : ℝ)) u) := by
-- proof
  obtain ⟨g, hg_mem, hg_eq⟩ := hu
  set ej := EuclideanSpace.single j (1 : ℝ)
  set m : EuclideanSpace ℝ (Fin n) → ℂ := fun ξ =>
    (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
    (↑(japaneseBracket n ξ))⁻¹
  refine ⟨fun ξ => m ξ * g ξ, ?_, ?_⟩
  ·
    have hm_bound : ∀ ξ : EuclideanSpace ℝ (Fin n), ‖m ξ‖ ≤ 2 * Real.pi := by
      intro ξ
      show ‖(2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹‖ ≤ 2 * Real.pi
      have hjb_pos := japaneseBracket_pos n ξ
      have h_inner_le := abs_inner_single_le_japaneseBracket j ξ
      rw [norm_mul, norm_mul, norm_two_pi_I,
        Complex.norm_real, Real.norm_eq_abs,
        norm_inv, Complex.norm_real, Real.norm_of_nonneg hjb_pos.le]
      calc (2 * Real.pi) * |@inner ℝ _ _ ξ ej| * (japaneseBracket n ξ)⁻¹
        ≤ (2 * Real.pi) * japaneseBracket n ξ * (japaneseBracket n ξ)⁻¹ := by gcongr
        _ = 2 * Real.pi := by rw [mul_assoc, mul_inv_cancel₀ (ne_of_gt hjb_pos)]; ring
    have hle : ∀ ξ : EuclideanSpace ℝ (Fin n),
      ‖m ξ * g ξ‖ ≤ (2 * Real.pi) * ‖g ξ‖ := by
      intro ξ; rw [norm_mul]; exact mul_le_mul_of_nonneg_right (hm_bound ξ) (norm_nonneg _)
    have hm_cont : Continuous m := by
      show Continuous (fun ξ => (2 * ↑Real.pi * Complex.I) * ↑(@inner ℝ _ _ ξ ej) *
        (↑(japaneseBracket n ξ))⁻¹)
      refine Continuous.mul (Continuous.mul continuous_const ?_) ?_
      · exact Complex.continuous_ofReal.comp (Continuous.inner continuous_id continuous_const)
      · refine Continuous.inv₀ (Complex.continuous_ofReal.comp ?_) ?_
        · show Continuous (japaneseBracket n)
          unfold japaneseBracket; fun_prop
        · intro ξ; exact Complex.ofReal_ne_zero.mpr (japaneseBracket_ne_zero n ξ)
    exact hg_mem.of_le_mul
      (hm_cont.aestronglyMeasurable.mul hg_mem.1)
      (Filter.Eventually.of_forall hle)
  ·
    intro φ
    have heval : (𝓕 (distribDerivCLM (F := ℂ) ej u)) φ =
      (2 * ↑Real.pi * Complex.I) *
      ((𝓕 u) (SchwartzMap.smulLeftCLM ℂ (fun ξ => (↑(@inner ℝ _ _ ξ ej) : ℂ)) φ)) := by
      change (𝓕 (LineDeriv.lineDerivOpCLM ℂ _ ej u)) φ = _
      rw [show (LineDeriv.lineDerivOpCLM ℂ (𝓢'(EuclideanSpace ℝ (Fin n), ℂ)) ej u) =
        LineDeriv.lineDerivOp ej u from rfl]
      have := TemperedDistribution.fourier_lineDerivOp_eq u ej
      rw [this]; rfl
    rw [heval, hg_eq]
    dsimp only []
    simp_rw [← smul_eq_mul (a := (2 * ↑Real.pi * Complex.I)), ← integral_smul]
    congr 1; ext ξ; simp only [smul_eq_mul]
    have htemp : Function.HasTemperateGrowth (fun ξ : EuclideanSpace ℝ (Fin n) =>
      (↑(@inner ℝ _ _ ξ ej) : ℂ)) :=
      (Complex.ofRealCLM.comp ((innerSL ℝ).flip ej)).hasTemperateGrowth
    rw [SchwartzMap.smulLeftCLM_apply_apply htemp]; simp only [smul_eq_mul]
    have hjb_pos := japaneseBracket_pos n ξ
    have hjb_ne : (japaneseBracket n ξ : ℂ) ≠ 0 :=
      Complex.ofReal_ne_zero.mpr (ne_of_gt hjb_pos)
    simp only [sobolevWeight]
    have hws : ((japaneseBracket n ξ ^ (s - 1) : ℝ) : ℂ)⁻¹ *
      ((japaneseBracket n ξ : ℝ) : ℂ)⁻¹ =
      ((japaneseBracket n ξ ^ s : ℝ) : ℂ)⁻¹ := by
      rw [← Complex.ofReal_inv, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
        ← Complex.ofReal_inv]
      congr 1
      rw [← Real.rpow_neg hjb_pos.le, ← Real.rpow_neg hjb_pos.le,
        show (japaneseBracket n ξ)⁻¹ = japaneseBracket n ξ ^ ((-1 : ℝ)) from
          (Real.rpow_neg_one (japaneseBracket n ξ)).symm,
        ← Real.rpow_add hjb_pos]
      congr 1; linarith
    rw [← hws]; ring

end SobolevSpace

namespace SobolevSpace

/--
[memHs_iteratedPartialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma memHs_iteratedPartialDeriv
  {n : ℕ}
  {n : ℕ}
  {s : ℝ}
  {j : Fin n}
  {k : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : MemHs n s u) :
-- imply
  MemHs n (s - ↑k) (iteratedPartialDerivDistrib n j k u) := by
-- proof
  induction k with
  | zero =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_zero, id_eq,
      Nat.cast_zero, sub_zero]
    exact hu
  | succ k ih =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp]
    have h := memHs_distribDeriv j _ ih
    convert h using 1
    push_cast; ring

end SobolevSpace

namespace SobolevSpace

/--
[memHs_foldr_iteratedPartialDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma memHs_foldr_iteratedPartialDeriv
  {n : ℕ}
  {n : ℕ}
  {s : ℝ}
  {l : List (Fin n)}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : MemHs n s u) :
-- imply
  MemHs n (s - ↑(l.map (fun j => α j)).sum) (l.foldr (fun j acc => iteratedPartialDerivDistrib n j (α j) acc) u) := by
-- proof
  induction l with
  | nil =>
    simp only [List.foldr_nil, List.map_nil, List.sum_nil, Nat.cast_zero, sub_zero]
    exact hu
  | cons j l ih =>
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    have hstep := memHs_iteratedPartialDeriv j (α j) _ ih
    convert hstep using 1
    push_cast; ring

end SobolevSpace

namespace SobolevSpace

/--
[memHs_iteratedDistribDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma memHs_iteratedDistribDeriv
  {n : ℕ}
  {n : ℕ}
  {s : ℝ}
  {α : Fin n → ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : MemHs n s u) :
-- imply
  MemHs n (s - ↑(multiIndexOrder n α)) (iteratedDistribDeriv n α u) := by
-- proof
  unfold iteratedDistribDeriv multiIndexOrder
  exact memHs_foldr_iteratedPartialDeriv (List.finRange n) α u hu

end SobolevSpace

namespace SobolevSpace

/--
[iteratedDistribDeriv_zero](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma iteratedDistribDeriv_zero
  {n : ℕ}
  {n : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iteratedDistribDeriv n (fun _ : Fin n => 0) u = u := by
-- proof
  unfold iteratedDistribDeriv
  induction (List.finRange n) with
  | nil => rfl
  | cons j l ih =>
    simp only [List.foldr_cons, iteratedPartialDerivDistrib, Function.iterate_zero, id_eq]
    exact ih

end SobolevSpace

namespace SobolevSpace

/--
[allDerivMemL2_of_succ](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma allDerivMemL2_of_succ
  {n : ℕ}
  {n : ℕ}
  {m : ℕ}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : AllDerivMemL2 n (m + 1) u) :
-- imply
  AllDerivMemL2 n m u :=
-- proof
  fun α hα => hu α (Nat.le_succ_of_le hα)

end SobolevSpace

namespace SobolevSpace

/--
[distribDeriv_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma distribDeriv_comm
  {n : ℕ}
  {n : ℕ}
  {v w : EuclideanSpace ℝ (Fin n)}
  {T : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  distribDerivCLM (F := ℂ) v (distribDerivCLM (F := ℂ) w T) = distribDerivCLM (F := ℂ) w (distribDerivCLM (F := ℂ) v T) := by
-- proof
  ext φ
  simp only [distribDerivCLM_apply, map_neg, neg_neg]
  congr 1
  exact (SchwartzRepresentation.schwartz_lineDerivOp_comm v w φ).symm

end SobolevSpace

namespace SobolevSpace

/--
[iteratedPartialDerivDistrib_distribDeriv_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma iteratedPartialDerivDistrib_distribDeriv_comm
  {n : ℕ}
  {n : ℕ}
  {i : Fin n}
  {k : ℕ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iteratedPartialDerivDistrib n i k (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) = distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) (iteratedPartialDerivDistrib n i k u) := by
-- proof
  induction k generalizing u with
  | zero => simp [iteratedPartialDerivDistrib]
  | succ k ih =>
    simp only [iteratedPartialDerivDistrib, Function.iterate_succ, Function.comp_apply]
    rw [distribDeriv_comm (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) u]
    exact ih (distribDerivCLM (F := ℂ) (EuclideanSpace.single i 1) u)

end SobolevSpace

namespace SobolevSpace

/--
[foldr_iterPartialDeriv_distribDeriv_comm](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma foldr_iterPartialDeriv_distribDeriv_comm
  {n : ℕ}
  {n : ℕ}
  {l : List (Fin n)}
  {α : Fin n → ℕ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) = distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u) := by
-- proof
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.foldr_cons]
    rw [ih]
    exact iteratedPartialDerivDistrib_distribDeriv_comm i (α i) j _

end SobolevSpace

namespace SobolevSpace

/--
[foldr_update_eq](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma foldr_update_eq
  {n : ℕ}
  {n : ℕ}
  {l : List (Fin n)}
  {α : Fin n → ℕ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hj : j ∉ l) :
-- imply
  l.foldr (fun k acc => iteratedPartialDerivDistrib n k (Function.update α j (α j + 1) k) acc) u = l.foldr (fun k acc => iteratedPartialDerivDistrib n k (α k) acc) u := by
-- proof
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons]
    have hne : i ≠ j := fun h => hj (h ▸ .head l)
    rw [Function.update_of_ne hne, ih (fun hm => hj (List.mem_cons_of_mem i hm))]

end SobolevSpace

namespace SobolevSpace

/--
[iteratedDistribDeriv_distribDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma iteratedDistribDeriv_distribDeriv
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)} :
-- imply
  iteratedDistribDeriv n α (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) = iteratedDistribDeriv n (Function.update α j (α j + 1)) u := by
-- proof
  unfold iteratedDistribDeriv
  rw [foldr_iterPartialDeriv_distribDeriv_comm]
  suffices h : ∀ (l : List (Fin n)), l.Nodup → j ∈ l →
    distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1)
      (l.foldr (fun i acc => iteratedPartialDerivDistrib n i (α i) acc) u) =
    l.foldr (fun i acc => iteratedPartialDerivDistrib n i
      (Function.update α j (α j + 1) i) acc) u by
    exact h _ (List.nodup_finRange n) (List.mem_finRange j)
  intro l hnd hmem
  induction l with
  | nil => simp at hmem
  | cons i l ih =>
    simp only [List.foldr_cons]
    obtain ⟨hni, hndl⟩ := List.nodup_cons.mp hnd
    by_cases hij : i = j
    · subst hij
      simp only [Function.update_self]
      rw [foldr_update_eq l α i hni]
      show distribDerivCLM (F := ℂ) (EuclideanSpace.single i 1)
        (iteratedPartialDerivDistrib n i (α i) _) = iteratedPartialDerivDistrib n i (α i + 1) _
      simp only [iteratedPartialDerivDistrib, Function.iterate_succ', Function.comp_apply]
    · have hmem_l : j ∈ l := by
      obtain h | h := List.mem_cons.mp hmem
      · exact absurd h.symm hij
      · exact h
      rw [(iteratedPartialDerivDistrib_distribDeriv_comm i (α i) j _).symm,
        Function.update_of_ne hij]
      congr 1
      exact ih hndl hmem_l

end SobolevSpace

namespace SobolevSpace

/--
[multiIndexOrder_update](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma multiIndexOrder_update
  {n : ℕ}
  {n : ℕ}
  {α : Fin n → ℕ}
  {j : Fin n} :
-- imply
  multiIndexOrder n (Function.update α j (α j + 1)) = multiIndexOrder n α + 1 := by
-- proof
  simp only [multiIndexOrder]
  have hne : ∀ i, i ≠ j → Function.update α j (α j + 1) i = α i :=
    fun i hi => Function.update_of_ne hi _ _
  calc ∑ i, Function.update α j (α j + 1) i
    = Function.update α j (α j + 1) j +
      ∑ x ∈ Finset.univ.erase j, Function.update α j (α j + 1) x := by
        rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    _ = (α j + 1) + ∑ x ∈ Finset.univ.erase j, α x := by
      rw [Function.update_self]
      congr 1
      exact Finset.sum_congr rfl (fun i hi => hne i (Finset.ne_of_mem_erase hi))
    _ = (α j + ∑ x ∈ Finset.univ.erase j, α x) + 1 := by omega
    _ = ∑ i, α i + 1 := by rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]

end SobolevSpace

namespace SobolevSpace

/--
[allDerivMemL2_distribDeriv](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/DifferentialAnalysis/code/SobolevDerivatives.lean)
-/
@[path]
lemma allDerivMemL2_distribDeriv
  {n : ℕ}
  {n : ℕ}
  {m : ℕ}
  {j : Fin n}
  {u : 𝓢'(EuclideanSpace ℝ (Fin n), ℂ)}
-- given
  (hu : AllDerivMemL2 n (m + 1) u) :
-- imply
  AllDerivMemL2 n m (distribDerivCLM (F := ℂ) (EuclideanSpace.single j 1) u) := by
-- proof
  intro α hα
  rw [iteratedDistribDeriv_distribDeriv]
  exact hu _ (by rw [multiIndexOrder_update]; omega)
end SobolevSpace
section SobolevWeightL2
open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory
variable {n : ℕ}
/-- Multiplying the Fourier-side `L²` representative by the Sobolev weight `⟨·⟩` stays in `L²`, given derivative regularity. -/
end SobolevWeightL2
noncomputable section
open scoped SchwartzMap FourierTransform
open SobolevSpace TemperedDistributions TestFunctions MeasureTheory
namespace SobolevSpace
/-- Inductive step: if `u ∈ H^m` and every `∂_j u ∈ H^m`, then `u ∈ H^{m+1}`. -/
end SobolevSpace
end



-- created on 2026-10-23
