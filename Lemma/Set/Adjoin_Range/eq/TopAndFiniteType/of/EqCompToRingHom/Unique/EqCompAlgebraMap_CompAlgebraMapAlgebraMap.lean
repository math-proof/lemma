import Mathlib
import sympy.Basic


/--
[Algebra_adjoin_range_eq_top_and_finiteType_of_forall_existsUnique_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Algebra_adjoin_range_eq_top_and_finiteType_of_forall_existsUnique_comp_eq.lean)
-/
@[path]
private lemma main
  {A₀ : Type u} [CommRing A₀]
  {A : Type u} [CommRing A] [Algebra A₀ A]
  {B₀ : Type u} [CommRing B₀] [Algebra A₀ B₀]
  {B : Type u} [CommRing B] [Algebra A B]
  {φ : B₀ →+* B}
-- given
  (hφ : φ.comp (algebraMap A₀ B₀) = (algebraMap A B).comp (algebraMap A₀ A))
  (hUP : ∀ (T : Type u) [CommRing T] [Algebra A T] (g : B₀ →+* T),
    g.comp (algebraMap A₀ B₀) = (algebraMap A T).comp (algebraMap A₀ A) →
    ∃! h : B →ₐ[A] T, h.toRingHom.comp φ = g) :
-- imply
  Algebra.adjoin A (Set.range φ) = ⊤ ∧ (Algebra.FiniteType A₀ B₀ → Algebra.FiniteType A B) := by
-- proof
  classical
  have hφ' : ∀ a₀ : A₀, φ (algebraMap A₀ B₀ a₀) = algebraMap A B (algebraMap A₀ A a₀) :=
    fun a₀ => RingHom.congr_fun hφ a₀
  set S : Subalgebra A B := Algebra.adjoin A (Set.range φ) with hS
  have hmemS : ∀ b₀ : B₀, φ b₀ ∈ S := fun b₀ => Algebra.subset_adjoin ⟨b₀, rfl⟩
  let g₀ : B₀ →+* S := φ.codRestrict S hmemS
  have hg₀ : g₀.comp (algebraMap A₀ B₀) = (algebraMap A S).comp (algebraMap A₀ A) := by
    ext a₀
    show φ (algebraMap A₀ B₀ a₀) = algebraMap A B (algebraMap A₀ A a₀)
    apply hφ' a₀
  obtain ⟨h, hh, -⟩ := hUP S g₀ hg₀
  have hgen : S = ⊤ := by
    obtain ⟨k, -, hk⟩ := hUP B φ hφ
    have hcomp : (S.val.comp h).toRingHom.comp φ = φ := by
      ext b₀
      show ((h (φ b₀) : S) : B) = φ b₀
      have this : h (φ b₀) = g₀ b₀ := RingHom.congr_fun hh b₀
      rw [this]
      rfl
    have h1 : (S.val.comp h) = k := hk _ hcomp
    have h2 : AlgHom.id A B = k := hk _ (by ext; rfl)
    rw [Algebra.eq_top_iff]
    intro b
    have hb : ((h b : S) : B) = b := by
      show (S.val.comp h) b = b
      rw [h1, ← h2]
      rfl
    rw [← hb]
    apply (h b).2
  refine ⟨hgen, ?_⟩
  intro hFT
  obtain ⟨s, hs⟩ := hFT.out
  refine ⟨⟨s.image φ, ?_⟩⟩
  rw [Algebra.eq_top_iff]
  have hsub : Set.range φ ⊆ (Algebra.adjoin A (↑(s.image φ) : Set B) : Subalgebra A B) := by
    rintro _ ⟨b₀, rfl⟩
    have hb₀ : b₀ ∈ Algebra.adjoin A₀ (↑s : Set B₀) := by
      rw [hs]
      trivial
    induction hb₀ using Algebra.adjoin_induction with
    | mem x hx =>
      apply Algebra.subset_adjoin
      simpa using Finset.mem_image_of_mem φ hx
    | algebraMap a₀ =>
      rw [hφ' a₀]
      apply Subalgebra.algebraMap_mem
    | add x y _ _ hx hy =>
      rw [map_add]
      apply add_mem hx hy
    | mul x y _ _ hx hy =>
      rw [map_mul]
      apply mul_mem hx hy
  intro b
  apply Algebra.adjoin_le hsub (show b ∈ S by rw [hgen]; apply Algebra.mem_top)


-- created on 2026-10-13
