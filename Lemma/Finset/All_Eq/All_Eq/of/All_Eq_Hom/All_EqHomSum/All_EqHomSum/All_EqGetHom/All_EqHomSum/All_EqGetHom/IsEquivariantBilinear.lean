import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.GroupCohomology.CupProduct
open CategoryTheory


/-- ported from external source -/
@[path]
private lemma main
  {k G : Type u} [CommRing k] [Group G]
  {S : Subgroup G} [S.FiniteIndex]
  {M D N : Rep.{u} k G}
  {φ : M →ₗ[k] D →ₗ[k] N}
  {ιM : M ⟶ Rep.coind S.subtype (Rep.res S.subtype M)}
  {τM : Rep.coind S.subtype (Rep.res S.subtype M) ⟶ M}
  {ιD : D ⟶ Rep.coind S.subtype (Rep.res S.subtype D)}
  {τD : Rep.coind S.subtype (Rep.res S.subtype D) ⟶ D}
  {τN : Rep.coind S.subtype (Rep.res S.subtype N) ⟶ N}
  {Ψ : Rep.coind S.subtype (Rep.res S.subtype M) →ₗ[k] Rep.coind S.subtype (Rep.res S.subtype D) →ₗ[k] N}
-- given
  (hφ : Rep.IsEquivariantBilinear M D N φ)
  (hιM : ∀ (m : M) (g : G), ((ιM.hom m : Rep.coind S.subtype (Rep.res S.subtype M)) : G → M) g = M.ρ g m)
  (hτM : ∀ f : Rep.coind S.subtype (Rep.res S.subtype M), τM.hom f = ∑ᶠ q : G ⧸ S, M.ρ q.out ((f : G → M) (q.out)⁻¹))
  (hιD : ∀ (d : D) (g : G), ((ιD.hom d : Rep.coind S.subtype (Rep.res S.subtype D)) : G → D) g = D.ρ g d)
  (hτD : ∀ f : Rep.coind S.subtype (Rep.res S.subtype D), τD.hom f = ∑ᶠ q : G ⧸ S, D.ρ q.out ((f : G → D) (q.out)⁻¹))
  (hτN : ∀ f : Rep.coind S.subtype (Rep.res S.subtype N), τN.hom f = ∑ᶠ q : G ⧸ S, N.ρ q.out ((f : G → N) (q.out)⁻¹))
  (hΨ : ∀ (f : Rep.coind S.subtype (Rep.res S.subtype M)) (g : Rep.coind S.subtype (Rep.res S.subtype D)) (w : Rep.coind S.subtype (Rep.res S.subtype N)), (∀ h : G, (w : G → N) h = φ ((f : G → M) h) ((g : G → D) h)) → Ψ f g = τN.hom w) :
-- imply
  (∀ (m : M) (y : Rep.coind S.subtype (Rep.res S.subtype D)), Ψ (ιM.hom m) y = φ m (τD.hom y)) ∧
    (∀ (x : Rep.coind S.subtype (Rep.res S.subtype M)) (d : D), Ψ x (ιD.hom d) = φ (τM.hom x) d) := by
  classical
    have : Finite (G ⧸ S) := Subgroup.finite_quotient_of_finiteIndex
    have : Fintype (G ⧸ S) := Fintype.ofFinite _
    have memW : ∀ (f : Rep.coind S.subtype (Rep.res S.subtype M)) (g : Rep.coind S.subtype (Rep.res S.subtype D)),
        (fun h : G => φ ((f : G → M) h) ((g : G → D) h)) ∈ Representation.coindV S.subtype (Rep.res S.subtype N).ρ := by
-- proof
      intro f g s h
      show φ ((f : G → M) ((s : G) * h)) ((g : G → D) ((s : G) * h)) = N.ρ (s : G) (φ ((f : G → M) h) ((g : G → D) h))
      have hf : (f : G → M) ((s : G) * h) = M.ρ (s : G) ((f : G → M) h) := f.2 s h
      have hg : (g : G → D) ((s : G) * h) = D.ρ (s : G) ((g : G → D) h) := g.2 s h
      rw [hf, hg]
      exact hφ (s : G) _ _
    refine ⟨fun m y => ?_, fun x d => ?_⟩
    ·
      rw [hΨ (ιM.hom m) y ⟨_, memW _ _⟩ (fun h => rfl), hτN, hτD, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        map_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      show N.ρ q.out (φ (((ιM.hom m : Rep.coind S.subtype (Rep.res S.subtype M)) : G → M) (q.out)⁻¹) ((y : G → D) (q.out)⁻¹)) = φ m (D.ρ q.out ((y : G → D) (q.out)⁻¹))
      rw [hιM, ← hφ q.out, ← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
    ·
      rw [hΨ x (ιD.hom d) ⟨_, memW _ _⟩ (fun h => rfl), hτN, hτM, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype,
        map_sum, LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun q _ => ?_
      show N.ρ q.out (φ ((x : G → M) (q.out)⁻¹) (((ιD.hom d : Rep.coind S.subtype (Rep.res S.subtype D)) : G → D) (q.out)⁻¹)) = φ (M.ρ q.out ((x : G → M) (q.out)⁻¹)) d
      rw [hιD, ← hφ q.out, ← Module.End.mul_apply (D.ρ _) (D.ρ _), ← map_mul, mul_inv_cancel, map_one,
        Module.End.one_apply]


-- created on 2026-10-23
