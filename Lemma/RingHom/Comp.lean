import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma c_t_apply {ι : Type} [Preorder ι] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) {L : Type} [CommRing L] (c : ∀ i, S i →+* L) (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i) {i j : ι} (h : i ≤ j) (y : S i) : c j (t i j h y) = c i y := by
  rw [← RingHom.comp_apply, hc]
private lemma t_t_apply {ι : Type} [Preorder ι] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk)) {i j k : ι} (hij : i ≤ j) (hjk : j ≤ k) (y : S i) : t j k hjk (t i j hij y) = t i k (hij.trans hjk) y := by
  rw [← RingHom.comp_apply, ht₂]
private lemma exists_lift_family {ι : Type} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) {L : Type} [CommRing L] (c : ∀ i, S i →+* L) (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i) (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x) {n : ℕ} (x : Fin n → L) : ∃ (I : ι) (y : Fin n → S I), ∀ k, c I (y k) = x k := by
  classical
  choose i y hy using fun k => hcsurj (x k)
  obtain ⟨I, hI⟩ := Finset.exists_le (Finset.univ.image i)
  exact ⟨I, fun k => t (i k) I (hI _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))) (y k), fun k => by rw [c_t_apply t c hc, hy]⟩
private lemma exists_forall_t_eq {ι : Type} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk)) {L : Type} [CommRing L] (c : ∀ i, S i →+* L) (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z) {I : ι} (s : Finset (S I)) (hs : ∀ r ∈ s, c I r = 0) : ∃ (J : ι) (hIJ : I ≤ J), ∀ r ∈ s, t I J hIJ r = 0 := by
  classical
  have key : ∀ r : s, ∃ (j : ι) (h : I ≤ j), t I j h r.1 = 0 := fun r => by
    obtain ⟨j, h, hj⟩ := hcker I r.1 0 (by rw [hs r.1 r.2, map_zero])
    exact ⟨j, h, by rw [hj, map_zero]⟩
  choose j hj hj0 using key
  obtain ⟨J, hJ⟩ := Finset.exists_le (insert I (Finset.univ.image j))
  have hIJ : I ≤ J := hJ I (Finset.mem_insert_self _ _)
  have hjJ : ∀ r, j r ≤ J := fun r => hJ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  refine ⟨J, hIJ, fun r hr => ?_⟩
  have := t_t_apply t ht₂ (hj ⟨r, hr⟩) (hjJ ⟨r, hr⟩) r
  rw [hj0 ⟨r, hr⟩, map_zero] at this
  rw [← this]
private lemma exists_comp_eq_of_finitePresentation {ι : Type} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk)) {L : Type} [CommRing L] (c : ∀ i, S i →+* L) (hc : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i) (hcsurj : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x) (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z) (A : Type) [CommRing A] [Algebra.FinitePresentation ℤ A] (u : A →+* L) : ∃ (j : ι) (ψ : A →+* S j), (c j).comp ψ = u := by
  classical
  obtain ⟨n, π, hπ, hker⟩ := (inferInstance : Algebra.FinitePresentation ℤ A).out
  obtain ⟨s, hs⟩ := hker
  obtain ⟨I, y, hy⟩ := exists_lift_family t c hc hcsurj (fun k => u (π (MvPolynomial.X k)))
  let σ : MvPolynomial (Fin n) ℤ →+* S I := MvPolynomial.eval₂Hom (Int.castRingHom (S I)) y
  have hσ : (c I).comp σ = u.comp π.toRingHom := by
    apply MvPolynomial.ringHom_ext
    ·
      intro z
      simp [σ]
    ·
      intro k
      simp [σ, hy]
  have hkerσ : ∀ r ∈ s.image σ, c I r = 0 := by
    intro r hr
    obtain ⟨p, hp, hpσ⟩ := Finset.mem_image.mp hr
    have : p ∈ RingHom.ker π.toRingHom := hs ▸ Ideal.subset_span hp
    rw [← hpσ, ← RingHom.comp_apply, hσ, RingHom.comp_apply, RingHom.mem_ker.mp this, map_zero]
  obtain ⟨J, hIJ, hJ⟩ := exists_forall_t_eq t ht₂ c hcker (s.image σ) hkerσ
  let σJ : MvPolynomial (Fin n) ℤ →+* S J := (t I J hIJ).comp σ
  have hvan : ∀ p ∈ RingHom.ker π.toRingHom, σJ p = 0 := by
    intro p hp
    rw [← hs] at hp
    refine Submodule.span_induction (p := fun p _ => σJ p = 0) ?_ ?_ ?_ ?_ hp
    ·
      intro r hr
      apply hJ _ (Finset.mem_image_of_mem σ hr)
    · apply map_zero _
    ·
      intro a b _ _ ha hb
      rw [map_add, ha, hb, add_zero]
    ·
      intro a b _ hb
      rw [smul_eq_mul, map_mul, hb, mul_zero]
  let e : (MvPolynomial (Fin n) ℤ ⧸ RingHom.ker π.toRingHom) ≃ₐ[ℤ] A := Ideal.quotientKerAlgEquivOfSurjective hπ
  let ψ : A →+* S J := (Ideal.Quotient.lift (RingHom.ker π.toRingHom) σJ hvan).comp e.symm.toAlgHom.toRingHom
  refine ⟨J, ψ, ?_⟩
  apply RingHom.ext
  intro a
  obtain ⟨p, hp⟩ := hπ a
  rw [← hp]
  have he : e.symm (π p) = Ideal.Quotient.mk _ p := by
    apply e.injective
    rw [AlgEquiv.apply_symm_apply]
    rfl
  have h1 : ψ (π p) = σJ p := by
    change Ideal.Quotient.lift (RingHom.ker π.toRingHom) σJ hvan (e.symm (π p)) = σJ p
    rw [he, Ideal.Quotient.lift_mk]
  have h2 := congrArg (fun φ : MvPolynomial (Fin n) ℤ →+* L => φ p) hσ
  simp only [RingHom.comp_apply] at h2
  rw [RingHom.comp_apply, h1]
  show c J (t I J hIJ (σ p)) = u (π p)
  rw [c_t_apply t c hc, h2]
  rfl
private lemma exists_comp_eq_comp_of_finiteType {ι : Type} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)] {S : ι → Type} [∀ i, CommRing (S i)] (t : ∀ i j, i ≤ j → (S i →+* S j)) (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk)) {L : Type} [CommRing L] (c : ∀ i, S i →+* L) (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z) (A : Type) [CommRing A] [Algebra.FiniteType ℤ A] {i : ι} (ψ ψ' : A →+* S i) (h : (c i).comp ψ = (c i).comp ψ') : ∃ (j : ι) (hij : i ≤ j), (t i j hij).comp ψ = (t i j hij).comp ψ' := by
  classical
  obtain ⟨s, hs⟩ := (inferInstance : Algebra.FiniteType ℤ A).out
  have key : ∀ a : s, ∃ (j : ι) (hij : i ≤ j), t i j hij (ψ a.1) = t i j hij (ψ' a.1) := fun a => hcker i _ _ (by rw [← RingHom.comp_apply, h, RingHom.comp_apply])
  choose j hij hj using key
  obtain ⟨J, hJ⟩ := Finset.exists_le (insert i (Finset.univ.image j))
  have hiJ : i ≤ J := hJ i (Finset.mem_insert_self _ _)
  have hjJ : ∀ a, j a ≤ J := fun a => hJ _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ (Finset.mem_univ _)))
  refine ⟨J, hiJ, ?_⟩
  have hgen : ∀ a ∈ (s : Set A), ((t i J hiJ).comp ψ) a = ((t i J hiJ).comp ψ') a := by
    intro a ha
    simp only [RingHom.comp_apply]
    rw [← t_t_apply t ht₂ (hij ⟨a, ha⟩) (hjJ ⟨a, ha⟩), ← t_t_apply t ht₂ (hij ⟨a, ha⟩) (hjJ ⟨a, ha⟩), hj ⟨a, ha⟩]
  show ((t i J hiJ).comp ψ).toIntAlgHom.toRingHom = ((t i J hiJ).comp ψ').toIntAlgHom.toRingHom
  refine congrArg (fun f : A →ₐ[ℤ] S J => f.toRingHom) ?_
  apply AlgHom.ext_of_adjoin_eq_top hs
  intro a ha
  apply hgen a ha
/--
[RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_RingHom_exists_comp_eq_comp_of_finiteType_of_directedSystem.lean)
-/
@[path]
private lemma main
  (ι : Type) [Preorder ι] [Nonempty ι] [IsDirected ι (· ≤ ·)]
  (S : ι → Type) [∀ i, CommRing (S i)]
  (t : ∀ i j, i ≤ j → (S i →+* S j))
  (L : Type) [CommRing L]
  (c : ∀ i, S i →+* L)
  (R : Type) [CommRing R] [Algebra.FiniteType ℤ R]
  (i : ι)
  (ψ ψ' : R →+* S i)
  -- given
  (_ : ∀ i (h : i ≤ i), t i i h = RingHom.id (S i))
  (ht₂ : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), (t j k hjk).comp (t i j hij) = t i k (hij.trans hjk))
  (_ : ∀ i j (h : i ≤ j), (c j).comp (t i j h) = c i)
  (_ : ∀ x : L, ∃ (i : ι) (y : S i), c i y = x)
  (hcker : ∀ (i : ι) (y z : S i), c i y = c i z → ∃ (j : ι) (h : i ≤ j), t i j h y = t i j h z)
  (h : (c i).comp ψ = (c i).comp ψ') :
  -- imply
  ∃ (j : ι) (hij : i ≤ j), (t i j hij).comp ψ = (t i j hij).comp ψ' :=
  exists_comp_eq_comp_of_finiteType t ht₂ c hcker R ψ ψ' h


-- created on 2026-10-20
