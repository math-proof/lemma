import Mathlib
import Structure.CerednikDrinfeld_SpecialFormalModule
import Structure.CerednikDrinfeld_GradedCartierModuleData
import Instance.CerednikDrinfeld_GradedCartierNModule

set_option autoImplicit false

noncomputable section

namespace CerednikDrinfeld

namespace GradedCartierModuleData

variable {p : ℕ} [Fact p.Prime] {B : Type} [CommRing B] {j : Zp2 p →+* B}
variable (D : GradedCartierModuleData p B j)


def Sigma (D : GradedCartierModuleData p B j) : Type := D.M

def toSigma : D.M ≃+ D.Sigma := AddEquiv.refl _

def ofSigma : D.Sigma ≃+ D.M := AddEquiv.refl _

@[simp] theorem ofSigma_toSigma (m : D.M) : D.ofSigma (D.toSigma m) = m := rfl

theorem smul_toSigma (w : WittVector p B) (m : D.M) :
    w • D.toSigma m = D.toSigma (WittVector.frobenius w • m) := rfl

theorem ofSigma_smul (w : WittVector p B) (m : D.Sigma) :
    D.ofSigma (w • m) = WittVector.frobenius w • D.ofSigma m := rfl

def nRelMap : D.Sigma →ₗ[WittVector p B] D.M × D.Sigma where
  toFun m := (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
  map_add' m m' := by
    simp only [map_add, map_neg, neg_add, Prod.mk_add_mk]
  map_smul' w m := by
    show (D.verschiebung (D.ofSigma (w • m)), D.toSigma (-D.varpi (D.ofSigma (w • m)))) =
      w • (D.verschiebung (D.ofSigma m), D.toSigma (-D.varpi (D.ofSigma m)))
    rw [Prod.smul_mk, ofSigma_smul, D.varpi_smul, D.smul_verschiebung, smul_toSigma, smul_neg]


def nRel : Submodule (WittVector p B) (D.M × D.Sigma) := LinearMap.range D.nRelMap

abbrev NMod : Type := (D.M × D.Sigma) ⧸ D.nRel

def nMk : D.M × D.M →+ D.NMod :=
  (D.nRel.mkQ.toAddMonoidHom).comp (AddMonoidHom.prodMap (AddMonoidHom.id D.M) D.toSigma.toAddMonoidHom)


def lambda : D.NMod →ₗ[WittVector p B] D.M :=
  D.nRel.liftQ
    { toFun := fun x => D.varpi x.1 + D.verschiebung (D.ofSigma x.2)
      map_add' := fun x y => by
        simp only [Prod.fst_add, Prod.snd_add, map_add]; abel
      map_smul' := fun w x => by
        simp only [Prod.smul_fst, Prod.smul_snd, map_smul, ofSigma_smul, RingHom.id_apply, smul_add,
          D.smul_verschiebung] }
    (by
      rintro x ⟨m, rfl⟩
      show D.varpi (D.verschiebung (D.ofSigma m)) + D.verschiebung (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m)))) = 0
      rw [ofSigma_toSigma, map_neg, D.varpi_verschiebung, add_neg_cancel])


def nMap {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) (hV : ∀ x, f (D.verschiebung x) = D'.verschiebung (f x))
    (hPi : ∀ x, f (D.varpi x) = D'.varpi (f x)) : D.NMod →+ D'.NMod :=
  QuotientAddGroup.map D.nRel.toAddSubgroup D'.nRel.toAddSubgroup
    (AddMonoidHom.prodMap f (D'.toSigma.toAddMonoidHom.comp (f.comp D.ofSigma.toAddMonoidHom))) (by
    rintro x ⟨m, rfl⟩
    refine ⟨D'.toSigma (f (D.ofSigma m)), ?_⟩
    show (D'.verschiebung (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))),
        D'.toSigma (-D'.varpi (D'.ofSigma (D'.toSigma (f (D.ofSigma m)))))) =
      (f (D.verschiebung (D.ofSigma m)), D'.toSigma (f (D.ofSigma (D.toSigma (-D.varpi (D.ofSigma m))))))
    simp only [ofSigma_toSigma, hV, map_neg, hPi])


def IsBaseChangeAlong' {B' : Type} [CommRing B'] {j' : Zp2 p →+* B'} (φ : B →+* B')
    (D : GradedCartierModuleData p B j) (D' : GradedCartierModuleData p B' j')
    (f : D.M →+ D'.M) : Prop :=
  (∀ (w : WittVector p B) (x : D.M), f (w • x) = WittVector.map φ w • f x) ∧
  (∀ x, f (D.frobenius x) = D'.frobenius (f x)) ∧
  (∀ x, f (D.verschiebung x) = D'.verschiebung (f x)) ∧
  (∀ x, f (D.varpi x) = D'.varpi (f x)) ∧
  (∀ (i : Fin 2) (x : D.M), x ∈ D.piece i → f x ∈ D'.piece i) ∧
  (∃ γ : Fin 2 → D.M, D.IsHomogeneousVBasis γ ∧ D'.IsHomogeneousVBasis (fun i => f (γ i)))

structure IsCartierLMap (L : D.M →+ D.NMod) : Prop where
  map_smul : ∀ (w : WittVector p B) (x : D.M), L (w • x) = WittVector.frobenius w • L x
  map_verschiebung : ∀ x : D.M, L (D.verschiebung x) = D.nMk (D.varpi x, 0)
  lambda_comp : ∀ x : D.M, D.lambda (L x) = D.frobenius x

structure IsCanonicalLMap (L : D.M →+ D.NMod) : Prop where
  isCartierLMap : D.IsCartierLMap L
  exists_lift : ∃ (S : Type) (_ : CommRing S) (jS : Zp2 p →+* S) (φ : S →+* B)
    (_ : Function.Surjective φ) (_ : ∀ s : S, (p : S) * s = 0 → s = 0)
    (Dl : GradedCartierModuleData p S jS) (_ : Dl.IsSpecialCartierModule)
    (f : Dl.M →+ D.M) (hf : IsBaseChangeAlong' φ Dl D f)
    (Ll : Dl.M →+ Dl.NMod) (_ : Dl.IsCartierLMap Ll),
    ∀ x : Dl.M, L (f x) = Dl.nMap D f hf.2.2.1 hf.2.2.2.1 (Ll x)


end GradedCartierModuleData

end CerednikDrinfeld

end
