import Mathlib
import Initialize.Tactic.Attr.Basic


/--
[Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_exists_algHom_adjoin_range_apply_eq_of_forall_sum_smul_eq_zero_of_algebra.lean)
-/
@[path]
private lemma main
  [Field K]
  [CommRing F] [Algebra K F]
  [CommRing L] [Algebra K L]
  {ι : Type u}
  {t : ι → F}
  {a : ι → L}
-- given
  (hone : ∃ i₀, t i₀ = 1 ∧ a i₀ = 1)
  (hmul : ∀ i j, ∃ k, t k = t i * t j ∧ a k = a i * a j)
  (hcons : ∀ (n : ℕ) (idx : Fin n → ι) (c : Fin n → K),
    ∑ l, c l • t (idx l) = 0 → ∑ l, c l • a (idx l) = 0) :
-- imply
  ∃ χ : ↥(Algebra.adjoin K (Set.range t)) →ₐ[K] L,
    ∀ i, χ ⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩ = a i := by
-- proof
  classical
  obtain ⟨i₀, ht₀, ha₀⟩ := hone
  set S : Subalgebra K F := Algebra.adjoin K (Set.range t) with hS
  have hclos : ((Submonoid.closure (Set.range t)) : Set F) = Set.range t := by
    let M : Submonoid F :=
      { carrier := Set.range t
        mul_mem' := by
          rintro _ _ ⟨i, rfl⟩ ⟨j, rfl⟩
          obtain ⟨k, hk, -⟩ := hmul i j
          refine ⟨k, hk⟩
        one_mem' := by
          refine ⟨i₀, ht₀⟩ }
    show ((Submonoid.closure (M : Set F)) : Set F) = (M : Set F)
    rw [Submonoid.closure_eq]
  have hSspan : S.toSubmodule = Submodule.span K (Set.range t) := by
    rw [hS, Algebra.adjoin_eq_span, hclos]
  let Lt : (Finsupp ι K) →ₗ[K] F := Finsupp.linearCombination K t
  let La : (Finsupp ι K) →ₗ[K] L := Finsupp.linearCombination K a
  have hLt : ∀ l : Finsupp ι K, Lt l = ∑ i ∈ l.support, l i • t i := fun l => by
    simp only [Lt, Finsupp.linearCombination_apply, Finsupp.sum]
  have hLa : ∀ l : Finsupp ι K, La l = ∑ i ∈ l.support, l i • a i := fun l => by
    simp only [La, Finsupp.linearCombination_apply, Finsupp.sum]
  have hker : LinearMap.ker Lt ≤ LinearMap.ker La := by
    intro l hl
    rw [LinearMap.mem_ker] at hl ⊢
    rw [hLt] at hl
    rw [hLa]
    let e := l.support.equivFin
    have h1 : ∑ m : Fin l.support.card, l (e.symm m : ι) • t (e.symm m : ι) =
        ∑ i ∈ l.support, l i • t i := by
      rw [← Finset.sum_coe_sort l.support (fun i => l i • t i)]
      apply Fintype.sum_equiv e.symm (fun m => l (e.symm m : ι) • t (e.symm m : ι))
        (fun i => l (i : ι) • t (i : ι))
      intro
      rfl
    have h2 : ∑ m : Fin l.support.card, l (e.symm m : ι) • a (e.symm m : ι) =
        ∑ i ∈ l.support, l i • a i := by
      rw [← Finset.sum_coe_sort l.support (fun i => l i • a i)]
      apply Fintype.sum_equiv e.symm (fun m => l (e.symm m : ι) • a (e.symm m : ι))
        (fun i => l (i : ι) • a (i : ι))
      intro
      rfl
    rw [← h2]
    apply hcons _ (fun m => (e.symm m : ι)) (fun m => l (e.symm m : ι))
    rw [h1, hl]
  have hrange : LinearMap.range Lt = S.toSubmodule := by
    rw [hSspan]
    apply Finsupp.range_linearCombination K
  have hmemS : ∀ s : ↥S, (s : F) ∈ LinearMap.range Lt := fun s => by
    rw [hrange]
    apply s.2
  let φ₀ : ((Finsupp ι K) ⧸ LinearMap.ker Lt) →ₗ[K] L := (LinearMap.ker Lt).liftQ La hker
  let eqv := Lt.quotKerEquivRange
  let φ : ↥S →ₗ[K] L :=
    { toFun := fun s => φ₀ (eqv.symm ⟨(s : F), hmemS s⟩)
      map_add' := by
        intro x y
        rw [← map_add φ₀, ← map_add eqv.symm]
        rfl
      map_smul' := by
        intro c x
        rw [RingHom.id_apply, ← map_smul φ₀, ← map_smul eqv.symm]
        rfl }
  have hφ : ∀ (s : ↥S) (l : Finsupp ι K), (s : F) = Lt l → φ s = La l := by
    intro s l hsl
    show φ₀ (eqv.symm ⟨(s : F), hmemS s⟩) = La l
    have : eqv.symm ⟨(s : F), hmemS s⟩ = Submodule.Quotient.mk l := by
      rw [LinearEquiv.symm_apply_eq]
      apply Subtype.ext
      show (s : F) = (Lt.quotKerEquivRange (Submodule.Quotient.mk l) : F)
      rw [LinearMap.quotKerEquivRange_apply_mk]
      apply hsl
    rw [this]
    apply Submodule.liftQ_apply _ _ l
  let v : ι → ↥S := fun i => ⟨t i, Algebra.subset_adjoin (Set.mem_range_self i)⟩
  have hφv : ∀ i, φ (v i) = a i := by
    intro i
    rw [hφ (v i) (Finsupp.single i 1) _]
    ·
      simp [La, Finsupp.linearCombination_single]
    ·
      simp [Lt, v, Finsupp.linearCombination_single]
  have hval : LinearMap.range (S.val.toLinearMap) = S.toSubmodule := by
    ext x
    constructor
    ·
      rintro ⟨s, rfl⟩
      apply s.2
    ·
      intro hx
      refine ⟨⟨x, hx⟩, rfl⟩
  have hv : Submodule.span K (Set.range v) = ⊤ := by
    apply Submodule.map_injective_of_injective (f := S.val.toLinearMap) (fun x y h => Subtype.ext h)
    rw [Submodule.map_span, Submodule.map_top, hval, hSspan, ← Set.range_comp]
    rfl
  have hmul' : ∀ x y : ↥S, φ (x * y) = φ x * φ y := by
    let B₁ : ↥S →ₗ[K] ↥S →ₗ[K] L := (LinearMap.mul K ↥S).compr₂ φ
    let B₂ : ↥S →ₗ[K] ↥S →ₗ[K] L := (LinearMap.mul K L).compl₁₂ φ φ
    have hB : B₁ = B₂ := by
      refine LinearMap.ext_on_range hv (fun i => LinearMap.ext_on_range hv (fun j => ?_))
      obtain ⟨k, hk, hak⟩ := hmul i j
      have hvk : v i * v j = v k := Subtype.ext hk.symm
      show φ (v i * v j) = φ (v i) * φ (v j)
      rw [hvk, hφv, hφv, hφv, hak]
    intro x y
    have := congrArg (fun B : ↥S →ₗ[K] ↥S →ₗ[K] L => B x y) hB
    apply this
  have hone' : φ 1 = 1 := by
    have : (1 : ↥S) = v i₀ := Subtype.ext ht₀.symm
    rw [this, hφv, ha₀]
  refine ⟨AlgHom.ofLinearMap φ hone' hmul', hφv⟩


-- created on 2026-10-13
