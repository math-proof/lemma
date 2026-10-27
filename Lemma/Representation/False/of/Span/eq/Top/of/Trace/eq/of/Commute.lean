import Mathlib
import Initialize.Tactic.Attr.Basic
open Module LinearMap
open Representation


private lemma false_of_span_eq_top_of_trace_eq_of_commute_impl
  {k G V V' : Type*} [Field k] [Monoid G]
  [AddCommGroup V] [Module k V] [FiniteDimensional k V]
  [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
  (h2 : Module.finrank k V = 2)
  (ρ : G →* Module.End k V) (hspan : Submodule.span k (Set.range ρ) = ⊤)
  (τ : G →* Module.End k V') (hcomm : ∀ g h : G, Commute (τ g) (τ h))
  (htr : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k V' (τ g)) : False := by
  classical
  set L : MonoidAlgebra k G →ₐ[k] Module.End k V := MonoidAlgebra.lift k (Module.End k V) G ρ
    with hL
  set L' : MonoidAlgebra k G →ₐ[k] Module.End k V' := MonoidAlgebra.lift k (Module.End k V') G τ
    with hL'
  have key : ∀ x : MonoidAlgebra k G, trace k V (L x) = trace k V' (L' x) := by
    intro x
    induction x using MonoidAlgebra.induction_on with
    | of g => simp [hL, hL', htr g]
    | add x y hx hy => simp [map_add, hx, hy]
    | smul r x hx => simp [map_smul, hx]
  have comm : ∀ x y : MonoidAlgebra k G, L' x * L' y = L' y * L' x := by
    intro x y
    induction x using MonoidAlgebra.induction_on with
    | of g =>
      induction y using MonoidAlgebra.induction_on with
      | of h => simpa [hL', MonoidAlgebra.lift_of] using (hcomm g h).eq
      | add y z hy hz => simp only [map_add, mul_add, add_mul, hy, hz]
      | smul r y hy => simp only [map_smul, mul_smul_comm, smul_mul_assoc, hy]
    | add x z hx hz => simp only [map_add, mul_add, add_mul, hx, hz]
    | smul r x hx => simp only [map_smul, mul_smul_comm, smul_mul_assoc, hx]
  have hsurj : Function.Surjective L := by
    have hle : Submodule.span k (Set.range ρ) ≤ LinearMap.range L.toLinearMap := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨g, rfl⟩
      exact ⟨MonoidAlgebra.of k G g, by simp [hL]⟩
    rwa [hspan, top_le_iff, LinearMap.range_eq_top] at hle
  let b : Basis (Fin 2) k V := Module.finBasisOfFinrankEq k V h2
  let E : Fin 2 → Fin 2 → Module.End k V := fun i j => (b.coord j).smulRight (b i)
  have hcoord : ∀ j l : Fin 2, b.coord j (b l) = if l = j then 1 else 0 := by
    intro j l
    simp [Basis.coord_apply, Finsupp.single_apply]
  have hE : ∀ i j l m : Fin 2, E i j * E l m = (b.coord j (b l)) • E i m := by
    intro i j l m
    refine LinearMap.ext fun v => ?_
    simp only [E, Module.End.mul_apply, LinearMap.smulRight_apply, LinearMap.smul_apply, map_smul,
      smul_smul, mul_comm]
  have hE' : ∀ i j l m : Fin 2, E i j * E l m = if l = j then E i m else 0 := by
    intro i j l m
    rw [hE, hcoord]
    split_ifs <;> simp
  have htrE : ∀ i j : Fin 2, trace k V (E i j) = if i = j then 1 else 0 := by
    intro i j
    simp only [E, trace_smulRight, hcoord]
  obtain ⟨r01, hr01⟩ := hsurj (E 0 1)
  obtain ⟨r10, hr10⟩ := hsurj (E 1 0)
  obtain ⟨r00, hr00⟩ := hsurj (E 0 0)
  have h1 : trace k V (L (r01 * r10 * r00)) = 1 := by
    rw [map_mul L, map_mul L, hr01, hr10, hr00, hE' 0 1 1 0, if_pos rfl, hE' 0 0 0 0,
      if_pos rfl, htrE, if_pos rfl]
  have h0 : trace k V (L (r10 * r01 * r00)) = 0 := by
    rw [map_mul L, map_mul L, hr01, hr10, hr00, hE' 1 0 0 1, if_pos rfl, hE' 1 1 0 0,
      if_neg Fin.zero_ne_one, map_zero]
  have hswap' : L' (r01 * r10 * r00) = L' (r10 * r01 * r00) := by
    rw [map_mul L', map_mul L', map_mul L', map_mul L', comm r01 r10]
  have hswap : trace k V (L (r01 * r10 * r00)) = trace k V (L (r10 * r01 * r00)) := by
    rw [key, key, hswap']
  rw [h1, h0] at hswap
  exact one_ne_zero hswap
/--
[Representation_false_of_span_eq_top_of_trace_eq_of_commute](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_Representation_false_of_span_eq_top_of_trace_eq_of_commute.lean)
-/
@[path]
private lemma main
  [Field k] [Monoid G] [AddCommGroup V] [Module k V] [FiniteDimensional k V] [AddCommGroup V'] [Module k V'] [FiniteDimensional k V']
  {ρ : G →* Module.End k V}
  {τ : G →* Module.End k V'}
-- given
  (h0 : Module.finrank k V = 2)
  (hspan : Submodule.span k (Set.range ρ) = ⊤)
  (hcomm : ∀ g h : G, Commute (τ g) (τ h))
  (htr : ∀ g : G, LinearMap.trace k V (ρ g) = LinearMap.trace k V' (τ g)) :
-- imply
  False :=
-- proof
  false_of_span_eq_top_of_trace_eq_of_commute_impl (h0 := h0) (ρ := ρ) (hspan := hspan) (τ := τ) (hcomm := hcomm) (htr := htr)


-- created on 2026-10-23
