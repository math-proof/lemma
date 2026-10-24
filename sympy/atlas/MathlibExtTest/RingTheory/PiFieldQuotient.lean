/- https://github.com/facebookresearch/atlas-lean/blob/main/MathlibExtTest/RingTheory/PiFieldQuotient.lean -/

-- MathlibExtTest/RingTheory/PiFieldQuotient.lean

import sympy.atlas.RingTheory.PiFieldQuotient
import Lemma.Int.PiFieldQuotient

open PiFieldQuotient

-- Restriction evaluates at the underlying index, definitionally.
example (x : ∀ _ : Fin 2, ℚ) (s : ({0} : Finset (Fin 2))) :
    restrict (K := ℚ) (F := fun _ : Fin 2 => ℚ) {0} x s = x s :=
  rfl

-- The surviving factor is selected by projection onto the first coordinate.
example : (0 : Fin 2) ∈ selected (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0) := by
  rw [mem_selected, eq_bot_iff]
  intro y hy
  rw [Ideal.mem_map_iff_of_surjective _ (Function.surjective_eval _)] at hy
  obtain ⟨x, hx, hxy⟩ := hy
  rw [RingHom.mem_ker] at hx
  rw [← hxy]
  exact hx

-- The killed factor is not selected by projection onto the first coordinate.
example : (1 : Fin 2) ∉ selected (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0) := by
  rw [mem_selected]
  intro htop
  have hmem : (Pi.single (1 : Fin 2) (1 : ℚ) : ∀ _ : Fin 2, ℚ) ∈
      RingHom.ker (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0) := by
    rw [RingHom.mem_ker]
    change (Pi.single (1 : Fin 2) (1 : ℚ) : ∀ _ : Fin 2, ℚ) 0 = 0
    exact Pi.single_eq_of_ne (by decide) _
  have h1 : (1 : ℚ) ∈
      Ideal.map (Pi.evalRingHom _ 1)
        (RingHom.ker (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0)) :=
    Ideal.mem_map_of_mem (Pi.evalRingHom _ (1 : Fin 2)) hmem
  rw [htop] at h1
  exact one_ne_zero ((Submodule.mem_bot _).mp h1)

-- A two-factor coordinate projection exhibits its target as a restricted product,
-- with the expected commuting equation.
example : ∃ S : Finset (Fin 2), ∃ e : ℚ ≃ₐ[ℚ] (∀ _ : S, ℚ),
    e.toAlgHom.comp (Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) 0) =
      AlgHom.pi (fun i : S => Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) ↑i) :=
  exists_algEquiv_restrict _ eval_zero_surjective

-- The weaker corollary on a two-factor coordinate projection.
example : ∃ S : Finset (Fin 2), Nonempty (ℚ ≃ₐ[ℚ] (∀ _ : S, ℚ)) :=
  exists_algEquiv _ eval_zero_surjective

-- The empty restriction has trivial target; the corollary still applies.
example : ∃ S : Finset (Fin 2),
    Nonempty ((∀ _ : (∅ : Finset (Fin 2)), ℚ) ≃ₐ[ℚ] (∀ _ : S, ℚ)) :=
  exists_algEquiv (restrict (K := ℚ) (F := fun _ : Fin 2 => ℚ) ∅)
    (restrict_surjective (∅ : Finset (Fin 2)))

-- The commuting equation on the empty restriction.
example : ∃ S : Finset (Fin 2),
    ∃ e : (∀ _ : (∅ : Finset (Fin 2)), ℚ) ≃ₐ[ℚ] (∀ _ : S, ℚ),
      e.toAlgHom.comp (restrict (K := ℚ) (F := fun _ : Fin 2 => ℚ) ∅) =
        AlgHom.pi (fun i : S => Pi.evalAlgHom ℚ (fun _ : Fin 2 => ℚ) ↑i) :=
  exists_algEquiv_restrict (restrict (K := ℚ) (F := fun _ : Fin 2 => ℚ) ∅)
    (restrict_surjective (∅ : Finset (Fin 2)))
