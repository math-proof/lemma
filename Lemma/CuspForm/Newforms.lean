import Def.FreyPackage_LevelRaising
import Instance.FLTPrelim_GaloisRep
import Instance.CuspForm_Newforms
import Def.CuspForm_Newforms

set_option autoImplicit false

noncomputable section

open WeierstrassCurve WeierstrassCurve.Affine.Point
open ModularFormClass

namespace CuspForm

variable {N : ℕ}


lemma GoodEigensystemOccursAt.refl {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2}
    (hf : f.IsNormalizedEigenform) : GoodEigensystemOccursAt f N :=
  ⟨f, hf, fun _ _ _ => rfl⟩


lemma IsNewform.isNormalizedEigenform {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) :
    f.IsNormalizedEigenform := hf.1

lemma IsNewform.ne_zero {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform) : f ≠ 0 :=
  hf.1.ne_zero


lemma IsNewform.isNewformAt {f : CuspForm (CongruenceSubgroup.Gamma0 N) 2} (hf : f.IsNewform)
    {q : ℕ} (hq : q.Prime) (hqN : q ∣ N) (hN : N ≠ 0) : f.IsNewformAt q :=
  ⟨hf.1, hqN, hf.2 (N / q) (Nat.div_dvd_of_dvd hqN)
    (Nat.div_lt_self (Nat.pos_of_ne_zero hN) hq.one_lt).ne⟩

end CuspForm

end
