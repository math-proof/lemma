import Mathlib
import sympy.Basic
set_option maxHeartbeats 999999
set_option synthInstance.maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false


private lemma smulCommClass
  {q : ℕ} [Fact q.Prime]
  {L : IntermediateField ℚ_[q] (PadicAlgCl q)}
  {G : Type} [Group G] [MulSemiringAction G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x) :
  -- imply
  SMulCommClass G ℚ_[q] L :=
  ⟨fun g c x => by rw [Algebra.smul_def, Algebra.smul_def, smul_mul', hG g c]⟩

/--
[ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ExtCitation_LocalLevel_finrank_eq_natCard_mul_finrank_of_forall_mem_iff_smul_eq.lean)
-/
@[path]
private lemma main
  (q : ℕ) [Fact q.Prime]
  (L : IntermediateField ℚ_[q] (PadicAlgCl q)) [FiniteDimensional ℚ_[q] L]
  (G : Type) [Group G] [Finite G] [MulSemiringAction G L] [FaithfulSMul G L]
  (hG : ∀ (g : G) (x : ℚ_[q]), g • algebraMap ℚ_[q] L x = algebraMap ℚ_[q] L x)
  (K : IntermediateField ℚ_[q] (PadicAlgCl q)) (hKL : K ≤ L)
  (hK : ∀ x : L, (x : PadicAlgCl q) ∈ K ↔ ∀ g : G, g • x = x) :
  -- imply
  Module.finrank ℚ_[q] L = Nat.card G * Module.finrank ℚ_[q] K := by
  -- proof
  classical
  let _ := smulCommClass hG
  let _ : Fintype G := Fintype.ofFinite G
  obtain ⟨E, hE⟩ : ∃ E : IntermediateField ℚ_[q] L, E = FixedPoints.intermediateField (F := ℚ_[q]) (E := L) G := ⟨_, rfl⟩
  have hmemE : ∀ x : L, x ∈ E ↔ ∀ g : G, g • x = x := fun x => by
    rw [hE]
    apply Iff.rfl
  have hArtin : Module.finrank E L = Fintype.card G := by
    subst hE
    apply FixedPoints.finrank_eq_card G L
  have hKE : Module.finrank ℚ_[q] K = Module.finrank ℚ_[q] E := by
    obtain ⟨φ, hφ⟩ : ∃ φ : K →ₗ[ℚ_[q]] E, ∀ x : K, ((φ x : L) : PadicAlgCl q) = (x : PadicAlgCl q) :=
      ⟨{ toFun := fun x => ⟨⟨(x : PadicAlgCl q), hKL x.2⟩, (hmemE _).mpr ((hK ⟨(x : PadicAlgCl q), hKL x.2⟩).mp x.2)⟩
         map_add' := fun x y => Subtype.ext (Subtype.ext rfl)
         map_smul' := fun c x => Subtype.ext (Subtype.ext (by simp [RingHom.id_apply])) },
       fun _ => rfl⟩
    have hinj : Function.Injective φ := by
      intro x y hxy
      apply Subtype.ext
      rw [← hφ x, ← hφ y, hxy]
    have hsurj : Function.Surjective φ := by
      intro y
      have hy : ((y : L) : PadicAlgCl q) ∈ K := (hK (y : L)).mpr ((hmemE _).mp y.2)
      refine ⟨⟨((y : L) : PadicAlgCl q), hy⟩, ?_⟩
      apply Subtype.ext
      apply Subtype.ext
      apply hφ _
    refine (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq
  rw [hKE, ← Module.finrank_mul_finrank ℚ_[q] E L, hArtin, Nat.card_eq_fintype_card, mul_comm]


-- created on 2026-10-20
