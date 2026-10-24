import Mathlib
import sympy.Basic
import sympy.atlas.v1.Atlas.AlgebraicGeometryI.code.HypersurfaceDim
open Ideal Polynomial


/--
[maximal_height_eq_of_field](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HypersurfaceDim.lean)
-/
@[path]
lemma maximal_height_eq_of_field
  {k : Type*}
  [Field k] :
-- imply
  ∀ (n : ℕ) (M : Ideal (MvPolynomial (Fin n) k)), M.IsMaximal → M.height = ↑n := by
-- proof
  intro n
  induction n with
  | zero =>
    intro M hM
    haveI : IsField (MvPolynomial (Fin 0) k) :=
      (MvPolynomial.isEmptyAlgEquiv k (Fin 0)).toRingEquiv.toMulEquiv.isField (Field.toIsField k)
    letI : Field (MvPolynomial (Fin 0) k) := ‹IsField _›.toField
    have hM_eq : M = ⊥ := (IsSimpleOrder.eq_bot_or_eq_top M).resolve_right hM.ne_top
    subst hM_eq; exact height_bot
  | succ m ih =>
    intro M hM
    let e := (MvPolynomial.finSuccEquiv k m).toRingEquiv
    let P := map (e : MvPolynomial (Fin (m + 1)) k ≃+* Polynomial (MvPolynomial (Fin m) k)) M
    haveI : P.IsMaximal := map_isMaximal_of_equiv e
    let M' := P.comap C
    haveI : M'.IsMaximal := isMaximal_comap_C_of_isJacobsonRing P
    haveI : P.LiesOver M' := ⟨rfl⟩
    rw [show M.height = P.height from (RingEquiv.height_map e M).symm,
      height_eq_height_add_one M' P, ih M' ‹_›]
    push_cast; ring

/--
[hypersurface_dim_n_minus_one](https://github.com/facebookresearch/atlas-lean/blob/main/v1/Atlas/AlgebraicGeometryI/code/HypersurfaceDim.lean)
-/
@[path]
lemma hypersurface_dim_n_minus_one
  {k : Type*}
  [Field k]
  {n : Nat}
  {f : MvPolynomial (Fin n) k}
-- given
  (hn : 0 < n)
  (hf0 : f ≠ 0)
  (hfu : ¬ IsUnit f) :
-- imply
  ringKrullDim (MvPolynomial (Fin n) k ⧸ Ideal.span {f}) = ↑(n - 1 : ℕ) := by
-- proof
  obtain ⟨M, hMmax, hfM⟩ := exists_le_maximal _ (span_singleton_ne_top hfu)
  have hfM' : f ∈ M := hfM (subset_span (Set.mem_singleton f))
  have hf_nzd : f ∈ nonZeroDivisors (MvPolynomial (Fin n) k) :=
    mem_nonZeroDivisors_of_ne_zero hf0
  have hM_height : M.height = ↑n := maximal_height_eq_of_field k n M hMmax
  have hdim : ringKrullDim (MvPolynomial (Fin n) k) = ↑n := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing]; simp
  haveI : M.IsPrime := hMmax.isPrime
  set d := ringKrullDim (MvPolynomial (Fin n) k ⧸ span {f})
  have hub : d + 1 ≤ ↑n := by
    calc d + 1 ≤ ringKrullDim (MvPolynomial (Fin n) k) :=
      ringKrullDim_quotient_succ_le_of_nonZeroDivisor hf_nzd
      _ = ↑n := hdim
  have hlb : (↑n : WithBot ℕ∞) ≤ d + 1 := by
    have h1 : (↑M.height : WithBot ℕ∞) ≤ d + 1 :=
      Ideal.height_le_ringKrullDim_quotient_add_one hfM'
    rwa [hM_height] at h1
  have heq : d + 1 = (↑n : WithBot ℕ∞) := le_antisymm hub hlb
  have hd_ne_bot : d ≠ ⊥ := by
    intro h; rw [h] at heq; simp at heq
  obtain ⟨d', hd'⟩ := WithBot.ne_bot_iff_exists.mp hd_ne_bot
  rw [← hd'] at heq ⊢
  have key' : d' + 1 = ↑n := by exact_mod_cast heq
  cases d' with
  | top => simp at key'
  | coe m =>
    have hm : m + 1 = n := by exact_mod_cast key'
    congr 1; exact_mod_cast show m = n - 1 by omega


-- created on 2026-10-23
