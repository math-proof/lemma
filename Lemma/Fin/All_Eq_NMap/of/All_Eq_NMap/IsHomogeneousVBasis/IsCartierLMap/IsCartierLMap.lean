import Mathlib
import sympy.Basic
import Lemma.CerednikDrinfeld.GradedCartierNModule
open CerednikDrinfeld CerednikDrinfeld.GradedCartierModuleData


/--
[CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_IsCartierLMap_comp_eq_nMap_comp_of_forall_apply_basis_eq.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {S B : Type} [CommRing S] [CommRing B]
  {jS : CerednikDrinfeld.Zp2 p →+* S}
  {j : CerednikDrinfeld.Zp2 p →+* B}
  {φ : S →+* B}
  {DS : CerednikDrinfeld.GradedCartierModuleData p S jS}
  {D : CerednikDrinfeld.GradedCartierModuleData p B j}
  {LS : DS.M →+ DS.NMod}
  {K : D.M →+ D.NMod}
  {γ : Fin 2 → DS.M}
-- given
  (h : DS.M →+ D.M)
  (hh : CerednikDrinfeld.GradedCartierModuleData.IsBaseChangeAlong' φ DS D h)
  (hLS : DS.IsCartierLMap LS)
  (hK : D.IsCartierLMap K)
  (hγ : DS.IsHomogeneousVBasis γ)
  (hKγ : ∀ i : Fin 2, K (h (γ i)) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS (γ i))) :
-- imply
  ∀ x : DS.M, K (h x) = DS.nMap D h hh.2.2.1 hh.2.2.2.1 (LS x) := by
-- proof
  classical
  set N := DS.nMap D h hh.2.2.1 hh.2.2.2.1 with hN
  have hσ : ∀ w : WittVector p S,
      WittVector.map φ (WittVector.frobenius w) = WittVector.frobenius (WittVector.map φ w) :=
    fun w => WittVector.IsPoly.map (WittVector.frobenius_isPoly p) φ w
  have hNsmul : ∀ (w : WittVector p S) (n : DS.NMod), N (w • n) = WittVector.map φ w • N n := by
    intro w n
    obtain ⟨⟨m, m'⟩, rfl⟩ := DS.nMk_surjective n
    rw [smul_nMk, hN, nMap_nMk, nMap_nMk, smul_nMk, hh.1, hh.1, hσ]
  have hV : ∀ y : DS.M, K (h (DS.verschiebung y)) = N (LS (DS.verschiebung y)) := by
    intro y
    rw [hh.2.2.1, hK.map_verschiebung, hLS.map_verschiebung, hN, nMap_nMk, hh.2.2.2.1, map_zero]
  have hT : ∀ (c : S) (i : Fin 2),
      K (h (WittVector.teichmuller p c • γ i)) = N (LS (WittVector.teichmuller p c • γ i)) := by
    intro c i
    rw [hh.1, hK.map_smul, hKγ i, hLS.map_smul, hNsmul, hσ]
  intro x
  obtain ⟨⟨c, y⟩, hx, -⟩ := hγ.2 x
  rw [hx]
  simp only [map_add, map_sum]
  rw [hV y]
  congr 1
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact hT (c i) i


-- created on 2026-10-24
