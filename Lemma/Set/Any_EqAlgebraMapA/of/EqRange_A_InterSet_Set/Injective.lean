import Mathlib
import sympy.Basic


/--
[ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_ValuationSubring_exists_ringEquiv_comap_of_range_eq_inter.lean)
-/
@[path]
private lemma main
  [CommRing A₀]
  {F L : Type*} [Field F] [Field L] [Algebra F L]
  {k₀ : IntermediateField F L}
  {A : ValuationSubring L}
  {ι : A₀ →+* ↥A}
-- given
  (hι : Function.Injective ι)
  (hιK₀ : Set.range (fun a : A₀ => ((ι a : ↥A) : L)) = (A : Set L) ∩ (k₀ : Set L)) :
-- imply
  ∃ e : A₀ ≃+* ↥(A.comap (algebraMap ↥k₀ L)),
      ∀ a : A₀, algebraMap ↥k₀ L ((e a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) = ((ι a : ↥A) : L) := by
-- proof
  classical
  have hk : ∀ a : A₀, ((ι a : ↥A) : L) ∈ (k₀ : Set L) := fun a =>
    (hιK₀ ▸ (Set.mem_range_self a : ((ι a : ↥A) : L) ∈ Set.range (fun a : A₀ => ((ι a : ↥A) : L)))).2
  have hA : ∀ a : A₀, ((ι a : ↥A) : L) ∈ A := fun a => (ι a).2
  let f : A₀ →+* ↥(A.comap (algebraMap ↥k₀ L)) :=
    { toFun := fun a => ⟨⟨((ι a : ↥A) : L), hk a⟩, show algebraMap ↥k₀ L ⟨((ι a : ↥A) : L), hk a⟩ ∈ A from hA a⟩
      map_one' := by apply Subtype.ext; apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp
      map_zero' := by apply Subtype.ext; apply Subtype.ext; simp
      map_add' := fun a b => by apply Subtype.ext; apply Subtype.ext; simp }
  have hf : ∀ a : A₀, (((f a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) = ((ι a : ↥A) : L) := fun _ => rfl
  have hinj : Function.Injective f := by
    intro a b h
    apply hι
    apply Subtype.ext
    have h' : (((f a : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) = (((f b : ↥(A.comap (algebraMap ↥k₀ L))) : ↥k₀) : L) :=
      congrArg (fun z : ↥(A.comap (algebraMap ↥k₀ L)) => ((z : ↥k₀) : L)) h
    rwa [hf, hf] at h'
  have hsurj : Function.Surjective f := by
    intro x
    have hx : ((x : ↥k₀) : L) ∈ (A : Set L) ∩ (k₀ : Set L) := ⟨x.2, (x : ↥k₀).2⟩
    rw [← hιK₀] at hx
    obtain ⟨a, ha⟩ := hx
    refine ⟨a, Subtype.ext (Subtype.ext ?_)⟩
    exact ha
  exact ⟨RingEquiv.ofBijective f ⟨hinj, hsurj⟩, fun a => hf a⟩


-- created on 2026-10-05
