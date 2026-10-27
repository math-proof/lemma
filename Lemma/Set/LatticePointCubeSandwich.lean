import Mathlib
import Initialize.Tactic.Attr.Basic
import Theorem.Geometry.LatticePointCubeSandwich.Part3
open MeasureTheory Set ENNReal Pointwise
open LatticePointCubeSandwich


namespace LatticePointCubeSandwich

/--
[innerCubeSet_subset_outerCubeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
lemma innerCubeSet_subset_outerCubeSet
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ} :
-- imply
  innerCubeSet S t ⊆ outerCubeSet S t := by
-- proof
  intro v hv
  rw [mem_innerCubeSet_iff] at hv
  rw [mem_outerCubeSet_iff]
  have hmem : (fun i => ((v i : ℤ) : ℝ)) ∈ integerUnitCube v := by
    rw [mem_integerUnitCube_iff]
    intro i
    exact ⟨le_refl _, by linarith⟩
  exact ⟨_, hmem, hv _ hmem⟩

end LatticePointCubeSandwich

namespace LatticePointCubeSandwich

/--
[finite_outerCubeSet](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
lemma finite_outerCubeSet
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
-- given
  (hS : Bornology.IsBounded S)
  (ht : 0 < t) :
-- imply
  (outerCubeSet S t).Finite := by
-- proof
  rw [isBounded_iff_forall_norm_le] at hS
  obtain ⟨R, hR⟩ := hS
  set B := ⌈R * t + 1⌉ with hB_def
  apply Set.Finite.subset (Set.Finite.pi (fun _ => Set.finite_Icc (-B) B))
  intro v hv
  rw [mem_outerCubeSet_iff] at hv
  obtain ⟨x, hxv, hx_mem⟩ := hv
  rw [mem_integerUnitCube_iff] at hxv
  simp only [mem_univ_pi, mem_Icc]
  intro i
  have hxt : ‖(fun j => x j / t)‖ ≤ R := hR _ hx_mem
  have hxi_t : |x i / t| ≤ R :=
    (norm_le_pi_norm (fun j => x j / t) i).trans hxt
  have hxi : |x i| ≤ R * t := by
    rwa [abs_div, div_le_iff₀ (abs_pos.mpr ht.ne'), abs_of_pos ht] at hxi_t
  obtain ⟨hlo, _hhi⟩ := hxv i
  have hxi_hi : x i ≤ R * t := (abs_le.mp hxi).2
  constructor
  · suffices h : -B < v i + 1 by omega
    suffices h : ((-B : ℤ) : ℝ) < (((v i + 1 : ℤ)) : ℝ) by
      exact_mod_cast h
    push_cast
    calc (-(⌈R * t + 1⌉ : ℤ) : ℝ) ≤ -(R * t + 1) := by
      linarith [Int.le_ceil (R * t + 1)]
      _ < (v i : ℝ) + 1 := by linarith [neg_le_of_abs_le hxi]
  · suffices h : (v i : ℤ) < B + 1 by omega
    suffices h : (((v i : ℤ)) : ℝ) < (((B + 1 : ℤ)) : ℝ) by
      exact_mod_cast h
    push_cast
    calc (v i : ℝ) ≤ x i := hlo
      _ ≤ R * t := hxi_hi
      _ < R * t + 1 := by linarith
      _ ≤ (⌈R * t + 1⌉ : ℤ) := Int.le_ceil _
      _ < (⌈R * t + 1⌉ : ℤ) + 1 := by linarith

end LatticePointCubeSandwich

namespace LatticePointCubeSandwich

/--
[cube_measure_sandwich](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
lemma cube_measure_sandwich
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
-- given
  (hS : Bornology.IsBounded S)
  (ht : 0 < t) :
-- imply
  (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n ∧
    (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
-- proof
  have ht_ne : t ≠ 0 := ne_of_gt ht
  have hS_vol : volume S ≠ ⊤ := ne_of_lt hS.measure_lt_top
  have hfin_outer : (outerCubeSet S t).Finite :=
    finite_outerCubeSet S hS ht
  have inner_sub_outer : innerCubeSet S t ⊆ outerCubeSet S t :=
    innerCubeSet_subset_outerCubeSet S t
  have hfin_inner := hfin_outer.subset inner_sub_outer
  have vol_cube : ∀ v : Fin n → ℤ, volume (integerUnitCube v) = 1 := by
    intro v
    simp only [integerUnitCube, Real.volume_pi_Ico, add_sub_cancel_left]
    simp [ENNReal.ofReal_one]
  have meas_cube : ∀ v : Fin n → ℤ,
    MeasurableSet (integerUnitCube v) :=
    fun v => MeasurableSet.pi Set.countable_univ (fun _ _ => measurableSet_Ico)
  have pd_all : Set.PairwiseDisjoint (Set.univ : Set (Fin n → ℤ))
    integerUnitCube := by
    intro v _ w _ hvw
    simp only [Function.onFun, Set.disjoint_left, mem_integerUnitCube_iff]
    intro x hxv hxw
    apply hvw
    funext i
    have hvi := (hxv i).1
    have hvi2 := (hxv i).2
    have hwi := (hxw i).1
    have hwi2 := (hxw i).2
    have : (v i : ℤ) = w i := by
      by_contra h
      obtain h' | h' := lt_or_gt_of_ne h
      · have : (v i : ℝ) + 1 ≤ (w i : ℝ) := by exact_mod_cast h'
        linarith
      · have : (w i : ℝ) + 1 ≤ (v i : ℝ) := by exact_mod_cast h'
        linarith
    exact_mod_cast this
  have vol_scaled : volume {x : Fin n → ℝ | (fun i => x i / t) ∈ S} =
    ENNReal.ofReal (t ^ n) * volume S := by
    have : {x : Fin n → ℝ | (fun i => x i / t) ∈ S} = t • S := by
      ext x
      simp only [mem_ofPred_eq, Set.mem_smul_set_iff_inv_smul_mem₀ ht_ne]
      suffices (fun i => x i / t) = t⁻¹ • x by rw [this]
      ext i
      simp [Pi.smul_apply, smul_eq_mul, inv_mul_eq_div]
    rw [this, Measure.addHaar_smul volume t S]
    congr 1
    rw [Module.finrank_pi_fintype]
    simp [Module.finrank_self, abs_of_pos (pow_pos ht n)]
  have measure_cubes : ∀ (T : Set (Fin n → ℤ)), T.Finite →
    volume (⋃ v ∈ T, integerUnitCube v) = (Nat.card T : ENNReal) := by
    intro T hT
    let _ : Fintype ↥T := hT.fintype
    rw [measure_biUnion hT.countable
      (fun i hi j hj hij => pd_all (mem_univ i) (mem_univ j) hij)
      (fun v _ => meas_cube v)]
    conv_lhs => arg 1; ext v; rw [vol_cube v.val]
    cases nonempty_fintype T
    simp [mul_one, Nat.card_eq_fintype_card]
  have h_left_ennreal : (Nat.card (innerCubeSet S t) : ENNReal) ≤
    ENNReal.ofReal (t ^ n) * volume S := by
    rw [← measure_cubes _ hfin_inner, ← vol_scaled]
    apply measure_mono
    intro x hx
    simp only [mem_iUnion, exists_prop] at hx
    obtain ⟨v, hv, hxv⟩ := hx
    exact (mem_innerCubeSet_iff.mp hv) x hxv
  have left_ineq :
    (Nat.card (innerCubeSet S t) : ℝ) ≤ (volume S).toReal * t ^ n := by
    have h := (ENNReal.toReal_le_toReal (ENNReal.natCast_ne_top _)
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)).mpr h_left_ennreal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith
  have h_right_ennreal : ENNReal.ofReal (t ^ n) * volume S ≤
    (Nat.card (outerCubeSet S t) : ENNReal) := by
    rw [← vol_scaled, ← measure_cubes _ hfin_outer]
    apply measure_mono
    intro x hx
    simp only [mem_iUnion, exists_prop]
    exact ⟨fun i => ⌊x i⌋,
      mem_outerCubeSet_iff.mpr ⟨x,
        mem_integerUnitCube_iff.mpr (fun i =>
          ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩), hx⟩,
      mem_integerUnitCube_iff.mpr (fun i =>
        ⟨Int.floor_le (x i), Int.lt_floor_add_one (x i)⟩)⟩
  have right_ineq :
    (volume S).toReal * t ^ n ≤ (Nat.card (outerCubeSet S t) : ℝ) := by
    have h := (ENNReal.toReal_le_toReal
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hS_vol)
      (ENNReal.natCast_ne_top _)).mpr h_right_ennreal
    rw [ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (by positivity : (0 : ℝ) ≤ t ^ n),
      ENNReal.toReal_natCast] at h
    linarith
  exact ⟨left_ineq, right_ineq⟩

end LatticePointCubeSandwich

/--
[mem_integerUnitCube_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_integerUnitCube_iff_eq
  {n : ℕ}
  {v : Fin n → ℤ}
  {x : Fin n → ℝ} :
-- imply
  x ∈ integerUnitCube v ↔ ∀ i, (v i : ℝ) ≤ x i ∧ x i < (v i : ℝ) + 1 := by
-- proof
  apply LatticePointCubeSandwich.mem_integerUnitCube_iff

/--
[mem_outerCubeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_outerCubeSet_iff_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
  {v : Fin n → ℤ} :
-- imply
  v ∈ outerCubeSet S t ↔ ∃ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S := by
-- proof
  apply LatticePointCubeSandwich.mem_outerCubeSet_iff

/--
[mem_innerCubeSet_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/Geometry/LatticePointCubeSandwich.lean)
-/
@[path]
private lemma mem_innerCubeSet_iff_eq
  {n : ℕ}
  {S : Set (Fin n → ℝ)}
  {t : ℝ}
  {v : Fin n → ℤ} :
-- imply
  v ∈ innerCubeSet S t ↔ ∀ x ∈ integerUnitCube v, (fun i => x i / t) ∈ S := by
-- proof
  apply LatticePointCubeSandwich.mem_innerCubeSet_iff


-- created on 2026-10-20
-- updated on 2026-10-26
