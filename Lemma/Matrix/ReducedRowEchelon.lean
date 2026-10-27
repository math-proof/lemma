import Mathlib
import Initialize.Tactic.Attr.Basic
import Def.LinearAlgebra.Matrix.ReducedRowEchelon
open Matrix.IsReducedRowEchelon
open MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted


namespace Matrix.IsReducedRowEchelon

/--
[col_eq_single_of_isLeadingEntry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
lemma col_eq_single_of_isLeadingEntry
  [Zero R] [One R] [DecidableEq m] [LinearOrder m] [LT n]
  {A : Matrix m n R}
  {i : m}
  {c : n}
-- given
  (hA : A.IsReducedRowEchelon)
  (hc : A.IsLeadingEntry i c) :
-- imply
  A.col c = Pi.single i 1 := by
-- proof
  ext x
  by_cases hxi : x = i
  · subst x
    simpa using hA.eq_one hc
  · simpa [hxi] using hA.eq_zero_of_ne_of_isLeadingEntry hxi hc

end Matrix.IsReducedRowEchelon

namespace Matrix.IsReducedRowEchelon

/--
[submatrix_orderIso](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
lemma submatrix_orderIso
  [Zero R] [One R] [LinearOrder m] [LinearOrder n] [LinearOrder o]
  {A : Matrix m n R}
-- given
  (hA : A.IsReducedRowEchelon)
  (e : o ≃o n) :
-- imply
  (A.submatrix id e : Matrix m o R).IsReducedRowEchelon := by
-- proof
  let B : Matrix m o R := A.submatrix id e
  have liftLeading : ∀ {i : m} {c : o}, B.IsLeadingEntry i c →
    A.IsLeadingEntry i (e c) := by
    intro i c hc
    constructor
    · intro q hq
      have hk : e.symm q < c := by
        simpa using e.symm.strictMono hq
      have hzero := hc.1 (e.symm q) hk
      simpa only [B, Matrix.submatrix_apply, id_eq, e.apply_symm_apply] using hzero
    · simpa only [B, Matrix.submatrix_apply, id_eq] using hc.2
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hi j hz
    apply hA.isRowEchelon hi
    intro q hq
    have hk : e.symm q < j := by
      simpa using e.symm.strictMono hq
    have hzero := hz (e.symm q) hk
    simpa only [B, Matrix.submatrix_apply, id_eq, e.apply_symm_apply] using hzero
  · intro i c hc
    exact hA.eq_one (liftLeading hc)
  · intro i₁ i₂ c hi hc
    exact hA.eq_zero hi (liftLeading hc)
end
namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted
variable {K : Type*} [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m]
  [Fintype n] [LinearOrder n]


namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_castSucc](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [Fintype m] [DecidableEq m] in
private lemma rref_fin_castSucc {d : ℕ} (A : Matrix m (Fin (d + 1)) K)
  (hA : A.IsReducedRowEchelon) :
  (A.submatrix id Fin.castSucc : Matrix m (Fin d) K).IsReducedRowEchelon := by
  let C : Matrix m (Fin d) K := A.submatrix id Fin.castSucc
  have liftLeading : ∀ {i : m} {c : Fin d}, C.IsLeadingEntry i c →
    A.IsLeadingEntry i c.castSucc := by
    intro i c hc
    constructor
    · intro j hj
      let k : Fin d := ⟨j.val, (show j.val < c.val from hj).trans c.isLt⟩
      have hjk : Fin.castSucc k = j := Fin.ext rfl
      have hkc : k < c := hj
      simpa only [C, Matrix.submatrix_apply, id_eq, hjk] using hc.1 k hkc
    · simpa only [C, Matrix.submatrix_apply, id_eq] using hc.2
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hi j hz
    apply hA.isRowEchelon hi
    intro q hq
    let k : Fin d := ⟨q.val, (show q.val < j.val from hq).trans j.isLt⟩
    have hqk : Fin.castSucc k = q := Fin.ext rfl
    have hkj : k < j := hq
    simpa only [C, Matrix.submatrix_apply, id_eq, hqk] using hz k hkj
  · intro i c hc
    exact hA.eq_one (liftLeading hc)
  · intro i₁ i₂ c hi hc
    exact hA.eq_zero hi (liftLeading hc)

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_last_isLeadingEntry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [Fintype m] [DecidableEq m] [LinearOrder m] in
private lemma rref_fin_last_isLeadingEntry {d : ℕ} (A : Matrix m (Fin (d + 1)) K)
  {i : m}
  (hrow : (A.submatrix id Fin.castSucc : Matrix m (Fin d) K).row i = 0)
  (hi : A i (Fin.last d) ≠ 0) : A.IsLeadingEntry i (Fin.last d) := by
  refine ⟨?_, hi⟩
  intro j hj
  let k : Fin d := ⟨j.val, (show j.val < d from hj)⟩
  have hjk : Fin.castSucc k = j := Fin.ext rfl
  have hk := congrFun hrow k
  change A i (Fin.castSucc k) = 0 at hk
  simpa only [hjk] using hk

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_last_col_eq_single](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [Fintype m] in
private lemma rref_fin_last_col_eq_single {d : ℕ} (A : Matrix m (Fin (d + 1)) K)
  (hA : A.IsReducedRowEchelon) {i : m}
  (hrow : (A.submatrix id Fin.castSucc : Matrix m (Fin d) K).row i = 0)
  (hi : A i (Fin.last d) ≠ 0) : A.col (Fin.last d) = Pi.single i 1 :=
  hA.col_eq_single_of_isLeadingEntry (rref_fin_last_isLeadingEntry A hrow hi)

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_last_pivot_le_of_prefix_row_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [Fintype m] [DecidableEq m] in
private lemma rref_fin_last_pivot_le_of_prefix_row_eq_zero {d : ℕ}
  (A : Matrix m (Fin (d + 1)) K) (hA : A.IsReducedRowEchelon) {i x : m}
  (hi : A i (Fin.last d) ≠ 0)
  (hxrow : (A.submatrix id Fin.castSucc : Matrix m (Fin d) K).row x = 0) : i ≤ x := by
  by_contra hix
  have hxi : x < i := lt_of_not_ge hix
  apply hi
  apply hA.isRowEchelon hxi
  intro j hj
  let k : Fin d := ⟨j.val, (show j.val < d from hj)⟩
  have hjk : Fin.castSucc k = j := Fin.ext rfl
  have hk := congrFun hxrow k
  change A x (Fin.castSucc k) = 0 at hk
  simpa only [hjk] using hk

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_mulVec_eq_self_of_prefix_support](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_mulVec_eq_self_of_prefix_support {d : ℕ}
  (C : Matrix m (Fin d) K) (hC : C.IsReducedRowEchelon)
  (P : Matrix m m K) (hPC : P * C = C) (a : m → K)
  (ha : ∀ i : m, C.row i = 0 → a i = 0) : P.mulVec a = a := by
  classical
  have hsingle : ∀ i : m, C.row i ≠ 0 →
    P.mulVec (Pi.single i 1) = Pi.single i 1 := by
    intro i hi
    obtain ⟨c, hc⟩ := Matrix.row_ne_zero_iff_exists_isLeadingEntry.mp hi
    have hcol := hC.col_eq_single_of_isLeadingEntry hc
    calc
      P.mulVec (Pi.single i 1) = P.mulVec (C.col c) := congrArg P.mulVec hcol.symm
      _ = (P * C).col c := Matrix.col_mul_eq_mulVec_col.symm
      _ = C.col c := by rw [hPC]
      _ = Pi.single i 1 := hcol
  ext x
  change (∑ i, P x i * a i) = a x
  calc
    ∑ i, P x i * a i = ∑ i, if x = i then a i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : C.row i = 0
      · simp [ha i hi]
      · have hpi := congrFun (hsingle i hi) x
        rw [Matrix.mulVec_single_one] at hpi
        change P x i = (Pi.single i (1 : K) : m → K) x at hpi
        by_cases hxi : x = i
        · simpa [hxi] using congrArg (fun z ↦ z * a i) hpi
        · simpa [hxi] using congrArg (fun z ↦ z * a i) hpi
    _ = a x := by simp

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_last_col_eq_of_prefix_eq](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rref_fin_last_col_eq_of_prefix_eq {d : ℕ}
  (A B : Matrix m (Fin (d + 1)) K)
  (hA : A.IsReducedRowEchelon) (hB : B.IsReducedRowEchelon)
  (P : Matrix m m K) (hP : IsUnit P) (h : B = P * A)
  (hprefix : (A.submatrix id Fin.castSucc : Matrix m (Fin d) K) =
    B.submatrix id Fin.castSucc) : A.col (Fin.last d) = B.col (Fin.last d) := by
  classical
  let C : Matrix m (Fin d) K := A.submatrix id Fin.castSucc
  have hC : C.IsReducedRowEchelon := by
    simpa only [C] using rref_fin_castSucc A hA
  have hPC : P * C = C := by
    ext x j
    calc
      (P * C) x j = (P * A) x (Fin.castSucc j) := rfl
      _ = B x (Fin.castSucc j) := congrArg (fun M ↦ M x (Fin.castSucc j)) h.symm
      _ = C x j := by
        have hp := congrArg (fun M ↦ M x j) hprefix
        exact hp.symm
  have hlast : B.col (Fin.last d) = P.mulVec (A.col (Fin.last d)) := by
    rw [h, Matrix.col_mul_eq_mulVec_col]
  by_cases hnewA : ∃ i : m, C.row i = 0 ∧ A i (Fin.last d) ≠ 0
  · obtain ⟨i, hirow, hi⟩ := hnewA
    have hAcol : A.col (Fin.last d) = Pi.single i 1 :=
      rref_fin_last_col_eq_single A hA hirow hi
    have hnewB : ∃ k : m, C.row k = 0 ∧ B k (Fin.last d) ≠ 0 := by
      by_contra hn
      have holdB : ∀ k : m, C.row k = 0 → B k (Fin.last d) = 0 := by
        intro k hk
        by_contra hkB
        exact hn ⟨k, hk, hkB⟩
      have hfixB : P.mulVec (B.col (Fin.last d)) = B.col (Fin.last d) :=
        rref_mulVec_eq_self_of_prefix_support C hC P hPC _ holdB
      have hinj : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hP
      have hBA : B.col (Fin.last d) = A.col (Fin.last d) := by
        apply hinj
        calc
          P.mulVec (B.col (Fin.last d)) = B.col (Fin.last d) := hfixB
          _ = P.mulVec (A.col (Fin.last d)) := hlast
      apply hi
      have hbzero := holdB i hirow
      change B.col (Fin.last d) i = 0 at hbzero
      rwa [hBA] at hbzero
    obtain ⟨k, hkrow, hk⟩ := hnewB
    have hkrowB : (B.submatrix id Fin.castSucc : Matrix m (Fin d) K).row k = 0 := by
      rwa [← hprefix]
    have hirowB : (B.submatrix id Fin.castSucc : Matrix m (Fin d) K).row i = 0 := by
      rwa [← hprefix]
    have hBcol : B.col (Fin.last d) = Pi.single k 1 :=
      rref_fin_last_col_eq_single B hB hkrowB hk
    have hik : i ≤ k :=
      rref_fin_last_pivot_le_of_prefix_row_eq_zero A hA hi hkrow
    have hki : k ≤ i :=
      rref_fin_last_pivot_le_of_prefix_row_eq_zero B hB hk hirowB
    have : i = k := le_antisymm hik hki
    subst k
    exact hAcol.trans hBcol.symm
  · have holdA : ∀ i : m, C.row i = 0 → A i (Fin.last d) = 0 := by
    intro i hirow
    by_contra hi
    exact hnewA ⟨i, hirow, hi⟩
    have hfixA : P.mulVec (A.col (Fin.last d)) = A.col (Fin.last d) :=
      rref_mulVec_eq_self_of_prefix_support C hC P hPC _ holdA
    exact (hlast.trans hfixA).symm

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_fin_unique_of_rowEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rref_fin_unique_of_rowEquivalent :
  ∀ d : ℕ, ∀ (A B : Matrix m (Fin d) K),
    A.IsReducedRowEchelon → B.IsReducedRowEchelon →
    ∀ (P : Matrix m m K), IsUnit P → B = P * A → A = B := by
  intro d
  induction d with
  | zero =>
    intro A B _ _ _ _ _
    ext _ j
    exact Fin.elim0 j
  | succ d ih =>
    intro A B hA hB P hP h
    let C₁ : Matrix m (Fin d) K := A.submatrix id Fin.castSucc
    let C₂ : Matrix m (Fin d) K := B.submatrix id Fin.castSucc
    have hC₁ : C₁.IsReducedRowEchelon := by
      simpa only [C₁] using rref_fin_castSucc A hA
    have hC₂ : C₂.IsReducedRowEchelon := by
      simpa only [C₂] using rref_fin_castSucc B hB
    have hC : C₂ = P * C₁ := by
      ext x j
      have hj := congrArg (fun M ↦ M x (Fin.castSucc j)) h
      change B x (Fin.castSucc j) = (P * A) x (Fin.castSucc j) at hj
      exact hj
    have hprefix : C₁ = C₂ := ih C₁ C₂ hC₁ hC₂ P hP hC
    have hlast : A.col (Fin.last d) = B.col (Fin.last d) :=
      rref_fin_last_col_eq_of_prefix_eq A B hA hB P hP h (by
        simpa only [C₁, C₂] using hprefix)
    ext x j
    by_cases hj : j = Fin.last d
    · subst j
      exact congrFun hlast x
    · obtain ⟨k, hk⟩ := Fin.eq_castSucc_of_ne_last hj
      have hp := congrArg (fun M ↦ M x k) hprefix
      change A x (Fin.castSucc k) = B x (Fin.castSucc k) at hp
      simpa only [hk] using hp

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[mem_rrefPivotColumns_iff](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma mem_rrefPivotColumns_iff {V : Type*} [AddCommGroup V] [Module K V]
  (v : n → V) (j : n) :
  j ∈ rrefPivotColumns (K := K) v ↔ v j ∉ Submodule.span K (v '' Set.Iio j) := by
  classical
  simp [rrefPivotColumns]

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_mem_span_pivotColumns_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rref_mem_span_pivotColumns_le {V : Type*} [AddCommGroup V] [Module K V]
  (v : n → V) (j : n) :
  v j ∈ Submodule.span K
    (v '' {k | k ∈ rrefPivotColumns (K := K) v ∧ k ≤ j}) := by
  classical
  refine wellFounded_lt.induction (C := fun j ↦
    v j ∈ Submodule.span K
      (v '' {k | k ∈ rrefPivotColumns (K := K) v ∧ k ≤ j})) j ?_
  intro j ih
  by_cases hj : j ∈ rrefPivotColumns (K := K) v
  · exact Submodule.subset_span ⟨j, ⟨hj, le_rfl⟩, rfl⟩
  · have hjspan : v j ∈ Submodule.span K (v '' Set.Iio j) := by
    simpa only [mem_rrefPivotColumns_iff, not_not] using hj
    refine (Submodule.span_le.2 ?_) hjspan
    rintro _ ⟨k, hk, rfl⟩
    refine Submodule.span_mono ?_ (ih k hk)
    rintro _ ⟨p, ⟨hp, hpj⟩, rfl⟩
    exact ⟨p, ⟨hp, hpj.trans hk.le⟩, rfl⟩

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rrefPivotColumns_linearIndepOn](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rrefPivotColumns_linearIndepOn {V : Type*} [AddCommGroup V] [Module K V]
  (v : n → V) : LinearIndepOn K v (rrefPivotColumns (K := K) v : Set n) := by
  classical
  let S := rrefPivotColumns (K := K) v
  have h : ∀ t : Finset n, t ⊆ S → LinearIndepOn K v (t : Set n) := by
    intro t
    refine Finset.induction_on_max t ?_ ?_
    · intro _
      simp
    · intro a s hmax ih hs
      have hsa : s ⊆ S := fun _ hx ↦ hs (Finset.mem_insert_of_mem hx)
      have ha : a ∈ S := hs (Finset.mem_insert_self a s)
      have hnot : v a ∉ Submodule.span K (v '' (s : Set n)) := by
        intro hva
        apply (mem_rrefPivotColumns_iff v a).mp ha
        refine Submodule.span_mono ?_ hva
        rintro _ ⟨x, hx, rfl⟩
        exact ⟨x, hmax x hx, rfl⟩
      simpa only [Finset.coe_insert] using (ih hsa).insert hnot
  exact h S fun _ ↦ id

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_sumExtend_inl](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rref_sumExtend_inl {V ι : Type*} [AddCommGroup V] [Module K V]
  {v : ι → V} (h : LinearIndependent K v) (i : ι) :
  Module.Basis.sumExtend h (Sum.inl i) = v i := by
  simp only [Module.Basis.sumExtend, Module.Basis.extend, Set.domRestrict_id, Equiv.trans_def,
    Module.Basis.coe_reindex, Module.Basis.coe_mk, Function.comp_apply]
  change ((Equiv.ofInjective v h.injective) i : V) = v i
  rfl

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rrefPivotColumns_linearIndependent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
private lemma rrefPivotColumns_linearIndependent {V : Type*} [AddCommGroup V] [Module K V]
  (v : n → V) :
  LinearIndependent K (fun i : Fin (rrefPivotColumns (K := K) v).card ↦
    v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i)) := by
  let S := rrefPivotColumns (K := K) v
  have hS : LinearIndependent K (fun j : S ↦ v j) :=
    (rrefPivotColumns_linearIndepOn v).linearIndependent_restrict
  have h := hS.comp (S.orderIsoOfFin rfl) (S.orderIsoOfFin rfl).injective
  change LinearIndependent K (fun i : Fin S.card ↦ v ↑(S.orderIsoOfFin rfl i)) at h
  simpa only [S] using h

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rrefPivotColumns_card_le](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] [LinearOrder m] in
private lemma rrefPivotColumns_card_le (v : n → (m → K)) :
  (rrefPivotColumns (K := K) v).card ≤ Fintype.card m := by
  have h := (rrefPivotColumns_linearIndependent (K := K) v).fintype_card_le_finrank
  simpa only [Fintype.card_fin, Module.finrank_fintype_fun_eq_card] using h

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_exists_aligned_basis](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_exists_aligned_basis (v : n → (m → K)) :
  ∃ (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
    (b : Module.Basis m K (m → K)),
    ∀ i : Fin (rrefPivotColumns (K := K) v).card,
      b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
        v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i) := by
  classical
  let S := rrefPivotColumns (K := K) v
  let piv := fun i : Fin S.card ↦ v ↑(S.orderIsoOfFin rfl i)
  have hli : LinearIndependent K piv := by
    simpa only [S, piv] using rrefPivotColumns_linearIndependent (K := K) v
  have hcard : S.card ≤ Fintype.card m := by
    simpa only [S] using rrefPivotColumns_card_le (K := K) v
  let rows := fun i : Fin S.card ↦
    Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)
  let b₀ := Module.Basis.sumExtend hli
  let I := Fin S.card ⊕ Module.Basis.sumExtendIndex hli
  let _ : Finite I := Module.Finite.finite_basis b₀
  let _ : Fintype I := Fintype.ofFinite I
  have hcardI : Fintype.card m = Fintype.card I := by
    rw [← Module.finrank_fintype_fun_eq_card K, Module.finrank_eq_card_basis b₀]
  let e₀ : m ≃ I := Fintype.equivOfCardEq hcardI
  have hrows : Function.Injective rows :=
    (Fintype.orderIsoFinOfCardEq m rfl).injective.comp (Fin.castLE_injective hcard)
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair
    (fun i ↦ e₀ (rows i)) (fun i : Fin S.card ↦ Sum.inl i)
    (e₀.injective.comp hrows) Sum.inl_injective
  let e : m ≃ I := e₀.trans σ
  let b : Module.Basis m K (m → K) := b₀.reindex e.symm
  refine ⟨hcard, b, ?_⟩
  intro i
  rw [Module.Basis.reindex_apply]
  change b₀ (e (rows i)) = piv i
  rw [show e (rows i) = Sum.inl i from hσ i]
  exact rref_sumExtend_inl hli i

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_rows_strictMono](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_rows_strictMono {r : ℕ} (hcard : r ≤ Fintype.card m) :
  StrictMono (fun i : Fin r ↦
    Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) :=
  (Fintype.orderIsoFinOfCardEq m rfl).strictMono.comp (Fin.strictMono_castLE hcard)

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_exists_row_of_lt_active](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_exists_row_of_lt_active {r : ℕ} (hcard : r ≤ Fintype.card m)
  {x : m} {i : Fin r}
  (hxi : x < Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) :
  ∃ k : Fin r,
    Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard k) = x ∧ k < i := by
  let e := Fintype.orderIsoFinOfCardEq m rfl
  have hq : e.symm x < Fin.castLE hcard i := by
    simpa only [e, OrderIso.symm_apply_apply] using (e.symm.lt_iff_lt.mpr hxi)
  have hqval : (e.symm x).val < i.val := hq
  let k : Fin r := ⟨(e.symm x).val, hqval.trans i.isLt⟩
  refine ⟨k, ?_, ?_⟩
  · have hk : Fin.castLE hcard k = e.symm x := Fin.ext rfl
    rw [hk, e.apply_symm_apply]
  · exact hqval

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_coord_pivot](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_coord_pivot (v : n → (m → K))
  (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
  (b : Module.Basis m K (m → K))
  (hb : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
      v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i))
  (i k : Fin (rrefPivotColumns (K := K) v).card) :
  b.repr (v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl k))
    (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
    if i = k then 1 else 0 := by
  rw [← hb k, b.repr_self]
  simp [Finsupp.single_apply, (rref_rows_strictMono hcard).injective.eq_iff, eq_comm]

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_coord_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_coord_eq_zero (v : n → (m → K))
  (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
  (b : Module.Basis m K (m → K))
  (hb : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
      v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i))
  (x : m) (j : n)
  (hx : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    (↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i) : n) ≤ j →
      x ≠ Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) :
  b.repr (v j) x = 0 := by
  let S := rrefPivotColumns (K := K) v
  rw [← b.coord_apply]
  apply LinearMap.mem_ker.mp
  refine (Submodule.span_le.2 ?_) (rref_mem_span_pivotColumns_le v j)
  rintro _ ⟨p, ⟨hp, hpj⟩, rfl⟩
  let i := (S.orderIsoOfFin rfl).symm ⟨p, hp⟩
  have hip : (↑(S.orderIsoOfFin rfl i) : n) = p := by
    simp [i]
  have hpi : (↑(S.orderIsoOfFin rfl i) : n) ≤ j := hip.trans_le hpj
  change b.coord x (v p) = 0
  rw [← hip, ← hb i, b.coord_apply, b.repr_self]
  simp [hx i hpi]

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_active_isLeadingEntry](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_active_isLeadingEntry (v : n → (m → K))
  (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
  (b : Module.Basis m K (m → K))
  (hb : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
      v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i))
  (i : Fin (rrefPivotColumns (K := K) v).card) :
  Matrix.IsLeadingEntry (fun x j ↦ b.repr (v j) x)
    (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i))
    ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i) := by
  constructor
  · intro j hj
    apply rref_coord_eq_zero v hcard b hb
    intro k hkj heq
    have hik : i = k := (rref_rows_strictMono hcard).injective heq
    subst k
    exact (not_le_of_gt hj) hkj
  · change b.repr (v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i))
    (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) ≠ 0
    rw [rref_coord_pivot v hcard b hb i i]
    simp

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_inactive_row_eq_zero](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_inactive_row_eq_zero (v : n → (m → K))
  (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
  (b : Module.Basis m K (m → K))
  (hb : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
      v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i))
  (x : m)
  (hx : ¬ ∃ i : Fin (rrefPivotColumns (K := K) v).card,
    Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i) = x) :
  (fun j ↦ b.repr (v j) x) = 0 := by
  funext j
  apply rref_coord_eq_zero v hcard b hb
  intro i _ hxi
  exact hx ⟨i, hxi.symm⟩

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

variable [Field K]
variable {m n : Type*} [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
/--
[rref_coordinates_isReducedRowEchelon](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
omit [DecidableEq m] in
private lemma rref_coordinates_isReducedRowEchelon (v : n → (m → K))
  (hcard : (rrefPivotColumns (K := K) v).card ≤ Fintype.card m)
  (b : Module.Basis m K (m → K))
  (hb : ∀ i : Fin (rrefPivotColumns (K := K) v).card,
    b (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)) =
      v ↑((rrefPivotColumns (K := K) v).orderIsoOfFin rfl i)) :
  Matrix.IsReducedRowEchelon (fun i j ↦ b.repr (v j) i : Matrix m n K) := by
  let S := rrefPivotColumns (K := K) v
  let rows := fun i : Fin S.card ↦
    Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard i)
  let piv := fun i : Fin S.card ↦ (↑(S.orderIsoOfFin rfl i) : n)
  let R := fun i j ↦ b.repr (v j) i
  have hlead : ∀ i : Fin S.card, Matrix.IsLeadingEntry R (rows i) (piv i) := by
    intro i
    simpa only [R, rows, piv, S] using rref_active_isLeadingEntry v hcard b hb i
  have hzero : ∀ x : m, (¬ ∃ i : Fin S.card, rows i = x) → R x = 0 := by
    intro x hx
    simpa only [R, rows, S] using rref_inactive_row_eq_zero v hcard b hb x hx
  have hpiv : StrictMono piv := by
    intro i k hik
    exact (S.orderIsoOfFin rfl).strictMono hik
  refine ⟨?_, ?_, ?_⟩
  · intro i₁ i₂ hi j hz
    by_cases hi₂ : ∃ k : Fin S.card, rows k = i₂
    · obtain ⟨k, rfl⟩ := hi₂
      by_cases hj : j < piv k
      · exact (hlead k).1 j hj
      · have hpj : piv k ≤ j := le_of_not_gt hj
        obtain ⟨l, hlrow, hlk⟩ := rref_exists_row_of_lt_active hcard hi
        have hlj : piv l < j := (hpiv hlk).trans_le hpj
        have hz' : R i₁ (piv l) = 0 := hz (piv l) hlj
        exfalso
        apply (hlead l).2
        have hlrow' : rows l = i₁ := by simpa only [rows, S] using hlrow
        rwa [hlrow']
    · exact congrFun (hzero i₂ hi₂) j
  · intro i c hc
    by_cases hi : ∃ k : Fin S.card, rows k = i
    · obtain ⟨k, rfl⟩ := hi
      have hc' : Matrix.IsLeadingEntry R (rows k) c := hc
      have hcpiv : c = piv k := hc'.unique (hlead k)
      rw [hcpiv]
      change b.repr (v ↑(S.orderIsoOfFin rfl k))
        (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard k)) = 1
      rw [rref_coord_pivot v hcard b hb k k]
      simp
    · exact (hc.row_ne_zero (hzero i hi)).elim
  · intro i₁ i₂ c hi hc
    by_cases hi₂ : ∃ k : Fin S.card, rows k = i₂
    · obtain ⟨k, rfl⟩ := hi₂
      have hc' : Matrix.IsLeadingEntry R (rows k) c := hc
      have hcpiv : c = piv k := hc'.unique (hlead k)
      obtain ⟨l, hlrow, hlk⟩ := rref_exists_row_of_lt_active hcard hi
      have hlrow' : rows l = i₁ := by simpa only [rows, S] using hlrow
      rw [← hlrow', hcpiv]
      change b.repr (v ↑(S.orderIsoOfFin rfl k))
        (Fintype.orderIsoFinOfCardEq m rfl (Fin.castLE hcard l)) = 0
      rw [rref_coord_pivot v hcard b hb l k]
      simp [ne_of_lt hlk]
    · exact (hc.row_ne_zero (hzero i₂ hi₂)).elim

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

/--
[exists_isReducedRowEchelon_rowEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
lemma exists_isReducedRowEchelon_rowEquivalent
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {A : Matrix m n K} :
-- imply
  ∃ (R : Matrix m n K) (P : Matrix m m K),
    R.IsReducedRowEchelon ∧ IsUnit P ∧ R = P * A := by
-- proof
  classical
  let v := A.col
  obtain ⟨hcard, b, hb⟩ := rref_exists_aligned_basis (K := K) v
  let R : Matrix m n K := fun i j ↦ b.repr (v j) i
  let P : Matrix m m K := LinearMap.toMatrix' b.equivFun.toLinearMap
  have hR : R.IsReducedRowEchelon := by
    simpa only [R] using rref_coordinates_isReducedRowEchelon v hcard b hb
  have hP : IsUnit P := LinearMap.isUnit_toMatrix'_iff.mpr ⟨
    LinearMap.GeneralLinearGroup.ofLinearEquiv b.equivFun, rfl⟩
  have hPA : R = P * A := by
    ext i j
    change b.repr (A.col j) i =
      (LinearMap.toMatrix' b.equivFun.toLinearMap).mulVec (A.col j) i
    rw [LinearMap.toMatrix'_mulVec]
    rfl
  exact ⟨R, P, hR, hP, hPA⟩

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

/--
[isReducedRowEchelon_unique_of_rowEquivalent](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
lemma isReducedRowEchelon_unique_of_rowEquivalent
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {R₁ R₂ : Matrix m n K}
  {P : Matrix m m K}
-- given
  (h₁ : R₁.IsReducedRowEchelon)
  (h₂ : R₂.IsReducedRowEchelon)
  (hP : IsUnit P)
  (h : R₂ = P * R₁) :
-- imply
  R₁ = R₂ := by
-- proof
  let e : Fin (Fintype.card n) ≃o n := Fintype.orderIsoFinOfCardEq n rfl
  let A : Matrix m (Fin (Fintype.card n)) K := R₁.submatrix id e
  let B : Matrix m (Fin (Fintype.card n)) K := R₂.submatrix id e
  have hA : A.IsReducedRowEchelon := by
    simpa only [A] using h₁.submatrix_orderIso e
  have hB : B.IsReducedRowEchelon := by
    simpa only [B] using h₂.submatrix_orderIso e
  have hBA : B = P * A := by
    ext i j
    have hj := congrArg (fun M ↦ M i (e j)) h
    change R₂ i (e j) = (P * R₁) i (e j) at hj
    exact hj
  have hAB : A = B :=
    rref_fin_unique_of_rowEquivalent (Fintype.card n) A B hA hB P hP hBA
  ext i j
  have hij := congrArg (fun M ↦ M i (e.symm j)) hAB
  change R₁ i (e (e.symm j)) = R₂ i (e (e.symm j)) at hij
  simpa only [e.apply_symm_apply] using hij

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

namespace MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted

/--
[ker_mulVecLin_mul_left_isUnit](https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExt/LinearAlgebra/Matrix/ReducedRowEchelon.lean)
-/
@[path]
lemma ker_mulVecLin_mul_left_isUnit
  [Field K] [Fintype m] [DecidableEq m] [LinearOrder m] [Fintype n] [LinearOrder n]
  {P : Matrix m m K}
  {A : Matrix m n K}
-- given
  (hP : IsUnit P) :
-- imply
  LinearMap.ker (Matrix.mulVecLin (P * A)) = LinearMap.ker (Matrix.mulVecLin A) := by
-- proof
  ext x
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have hinj : Function.Injective P.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hP
  simpa only [Matrix.mulVecLin_apply, ← Matrix.mulVec_mulVec, Matrix.mulVec_zero] using
    (hinj.eq_iff (a := A.mulVec x) (b := 0))

end MathlibExt.LinearAlgebra.Matrix.ReducedRowEchelonWanted


-- created on 2026-10-20
-- updated on 2026-10-26
