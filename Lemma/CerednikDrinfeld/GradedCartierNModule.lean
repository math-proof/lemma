import Mathlib
import Lemma.CerednikDrinfeld.SpecialFormalModule
import Lemma.CerednikDrinfeld.GradedCartierModuleData
import Instance.CerednikDrinfeld_GradedCartierNModule
import Structure.CerednikDrinfeld_GradedCartierNModule
import Notation.CerednikDrinfeld_GradedCartierNModule

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)

open scoped CerednikDrinfeld_GradedCartierNModule


@[simp] theorem toSigma_ofSigma (m : D.Sigma) : D.toSigma (D.ofSigma m) = m := rfl


@[simp] theorem nRelMap_apply (m : D.Sigma) :
    D.nRelMap m = (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m))) := rfl


theorem nMk_apply (m m' : D.M) : D.nMk (m, m') = D.nRel.mkQ (m, D.toSigma m') := rfl

theorem nMk_surjective : Function.Surjective D.nMk := by
  intro z
  obtain ⟨⟨m, m'⟩, rfl⟩ := D.nRel.mkQ_surjective z
  exact ⟨(m, D.ofSigma m'), rfl⟩

theorem nMk_verschiebung_neg_varpi (m : D.M) : D.nMk (D.verschiebung m, -D.varpi m) = 0 := by
  rw [nMk_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact ⟨D.toSigma m, rfl⟩

theorem smul_nMk (w : WittVector p B) (m m' : D.M) :
    w • D.nMk (m, m') = D.nMk (w • m, WittVector.frobenius w • m') := rfl


@[simp] theorem lambda_nMk (m m' : D.M) : D.lambda (D.nMk (m, m')) = D.varpi m + D.verschiebung m' := rfl

def vRange : Submodule (WittVector p B) D.M where
  carrier := Set.range D.verschiebung
  zero_mem' := ⟨0, map_zero _⟩
  add_mem' := by
    rintro _ _ ⟨x, rfl⟩ ⟨y, rfl⟩
    exact ⟨x + y, map_add _ _ _⟩
  smul_mem' := by
    rintro w _ ⟨x, rfl⟩
    exact ⟨WittVector.frobenius w • x, (D.smul_verschiebung w x).symm⟩

theorem mem_vRange_iff (x : D.M) : x ∈ D.vRange ↔ ∃ y, D.verschiebung y = x := Iff.rfl

abbrev LieQuot : Type := D.M ⧸ D.vRange

def toLieQuot : D.NMod →ₗ[WittVector p B] D.LieQuot :=
  D.nRel.liftQ (D.vRange.mkQ.comp (LinearMap.fst _ _ _)) (by
    rintro x ⟨m, rfl⟩
    show D.vRange.mkQ (D.verschiebung (D.ofSigma m)) = 0
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact ⟨D.ofSigma m, rfl⟩)

def inrSigma : D.Sigma →ₗ[WittVector p B] D.NMod := D.nRel.mkQ.comp (LinearMap.inr _ _ _)

def nVarpi : D.NMod →ₗ[WittVector p B] D.NMod :=
  D.nRel.mapQ D.nRel
    (LinearMap.prodMap D.varpi
      { toFun := fun m => D.toSigma (D.varpi (D.ofSigma m))
        map_add' := fun x y => by simp only [map_add]
        map_smul' := fun w m => by rw [ofSigma_smul, map_smul, RingHom.id_apply, smul_toSigma] })
    (by
      rintro x ⟨m, rfl⟩
      refine ⟨D.toSigma (D.varpi (D.ofSigma m)), ?_⟩
      show (D.verschiebung (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))),
          D.toSigma (-D.varpi (D.ofSigma (D.toSigma (D.varpi (D.ofSigma m)))))) =
        (D.varpi (D.verschiebung (D.ofSigma m)), D.toSigma (D.varpi (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
      simp only [ofSigma_toSigma, D.varpi_verschiebung, map_neg])

def nPiece (i : Fin 2) : AddSubgroup D.NMod :=
  (((D.piece i).toAddSubgroup).prod ((D.piece i).toAddSubgroup)).map D.nMk


theorem nMap_nMk {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) (m m' : D.M) :
    D.nMap D' f hV hPi (D.nMk (m, m')) = D'.nMk (f m, f m') := rfl


def cartierL (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.M →+ D.NMod := h.choose

theorem cartierL_spec (h : ∃ L : D.M →+ D.NMod, D.IsCanonicalLMap L) : D.IsCanonicalLMap (D.cartierL h) :=
  h.choose_spec

def phi (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.NMod →+ D.NMod :=
  QuotientAddGroup.lift D.nRel.toAddSubgroup
    (AddMonoidHom.coprod L (D.nMk.comp ((AddMonoidHom.inl D.M D.M).comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    show L (D.verschiebung (D.ofSigma m)) + D.nMk (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))), 0) = 0
    rw [hL, ofSigma_toSigma, ← map_add, Prod.mk_add_mk, add_neg_cancel, add_zero]
    exact map_zero D.nMk)

theorem phi_nMk (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (x x' : D.M) : D.phi L hL (D.nMk (x, x')) = L x + D.nMk (x', 0) := rfl

def eta (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    AddSubgroup D.NMod :=
  (D.phi L hL - AddMonoidHom.id D.NMod).ker

theorem mem_eta_iff (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (z : D.NMod) : z ∈ D.eta L hL ↔ D.phi L hL z = z := by
  rw [eta, AddMonoidHom.mem_ker, AddMonoidHom.sub_apply, sub_eq_zero]
  rfl

def etaPiece (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0))
    (i : Fin 2) : AddSubgroup D.NMod :=
  D.eta L hL ⊓ D.nPiece i

def u (L : D.M →+ D.NMod) (hL : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)) :
    D.eta L hL →+ D.LieQuot :=
  D.toLieQuot.toAddMonoidHom.comp (D.eta L hL).subtype

end GradedCartierModuleData

end CerednikDrinfeld

end
