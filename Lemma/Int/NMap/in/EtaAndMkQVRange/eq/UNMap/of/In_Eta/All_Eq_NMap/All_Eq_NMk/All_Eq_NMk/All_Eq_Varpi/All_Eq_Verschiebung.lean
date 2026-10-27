import Mathlib
import Initialize.Tactic.Attr.Basic
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Lemma.CerednikDrinfeld.GradedCartierNModule
import Lemma.Int.P2MUtil


/--
[CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq](https://github.com/anthropics/fermats-last-theorem/blob/main/P2M/Sol/S_CerednikDrinfeld_GradedCartierModuleData_u_nMap_of_comp_eq.lean)
-/
@[path]
private lemma main
  {p : ℕ} [Fact p.Prime]
  {B B' : Type} [CommRing B] [CommRing B']
  {j : CerednikDrinfeld.Zp2 p →+* B}
  {j' : CerednikDrinfeld.Zp2 p →+* B'}
  {D : CerednikDrinfeld.GradedCartierModuleData p B j}
  {D' : CerednikDrinfeld.GradedCartierModuleData p B' j'}
  {bc : D.M →+ D'.M}
  {L : D.M →+ D.NMod}
  {L' : D'.M →+ D'.NMod}
  {z : D.NMod}
-- given
  (hV : ∀ x, bc (D.verschiebung x) = D'.verschiebung (bc x))
  (hPi : ∀ x, bc (D.varpi x) = D'.varpi (bc x))
  (hLV : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
  (hLV' : ∀ x : D'.M, L' (D'.verschiebung x) = D'.nMk (D'.varpi x, 0))
  (hLL' : ∀ x, L' (bc x) = D.nMap D' bc hV hPi (L x))
  (hz : z ∈ D.eta L hLV) :
-- imply
  D.nMap D' bc hV hPi z ∈ D'.eta L' hLV' ∧
      ∀ (m : D.M) (hz' : D.nMap D' bc hV hPi z ∈ D'.eta L' hLV'),
        D.vRange.mkQ m = D.u L hLV ⟨z, hz⟩ →
        D'.vRange.mkQ (bc m) = D'.u L' hLV' ⟨D.nMap D' bc hV hPi z, hz'⟩ := by
-- proof
  classical
  set N := D.nMap D' bc hV hPi with hN
  have hq : ∀ x x' : D.M, D.toLieQuot (D.nMk (x, x')) = D.vRange.mkQ x := fun x x' => rfl
  have hq' : ∀ x x' : D'.M, D'.toLieQuot (D'.nMk (x, x')) = D'.vRange.mkQ x := fun x x' => rfl
  have hphi : ∀ w : D.NMod, D'.phi L' hLV' (N w) = N (D.phi L hLV w) := by
    intro w
    obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective w
    rw [hN, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk, CerednikDrinfeld.GradedCartierModuleData.phi_nMk,
      CerednikDrinfeld.GradedCartierModuleData.phi_nMk, map_add, hLL', CerednikDrinfeld.GradedCartierModuleData.nMap_nMk,
      map_zero]
  have hmem : N z ∈ D'.eta L' hLV' := by
    rw [CerednikDrinfeld.GradedCartierModuleData.mem_eta_iff, hphi,
      (CerednikDrinfeld.GradedCartierModuleData.mem_eta_iff D L hLV z).mp hz]
  refine ⟨hmem, fun m hz' hm => ?_⟩
  obtain ⟨⟨x, x'⟩, rfl⟩ := D.nMk_surjective z
  have hu : D.u L hLV ⟨D.nMk (x, x'), hz⟩ = D.vRange.mkQ x := hq x x'
  have hu' : D'.u L' hLV' ⟨N (D.nMk (x, x')), hz'⟩ = D'.vRange.mkQ (bc x) := by
    show D'.toLieQuot (N (D.nMk (x, x'))) = _
    rw [hN, CerednikDrinfeld.GradedCartierModuleData.nMap_nMk]
    exact hq' (bc x) (bc x')
  rw [hu']
  rw [hu] at hm
  rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq] at hm ⊢
  obtain ⟨y, hy⟩ := (D.mem_vRange_iff _).mp hm
  refine (D'.mem_vRange_iff _).mpr ⟨bc y, ?_⟩
  rw [← hV, hy, map_sub]


-- created on 2026-10-24
