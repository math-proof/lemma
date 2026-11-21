import Def.Data.Tensor.Unsqueeze
import Lemma.Vector.ValCast.eq.Val.of.Eq
open List Vector


@[path]
private lemma main
  {s : List ℕ}
-- given
  (X : Tensor α s)
  (d : ℕ) :
-- imply
  X.unsqueeze d = ⟨cast (congrArg (List.Vector α) ((ProdInsertIdx.eq.Prod s d).symm)) X.data⟩ := by
-- proof
  apply congrArg Tensor.mk
  apply Subtype.ext
  have h_dvd : s.prod ∣ (s.insertIdx d 1).prod := by rw [ProdInsertIdx.eq.Prod]
  change (cast (congrArg (List.Vector α) (Nat.EqMulDiv.of.Dvd h_dvd))
    (X.data.repeat ((s.insertIdx d 1).prod / s.prod))).val =
    (cast (congrArg (List.Vector α) (ProdInsertIdx.eq.Prod s d).symm) X.data).val
  rw [ValCast.eq.Val.of.Eq (Nat.EqMulDiv.of.Dvd h_dvd),
    ValCast.eq.Val.of.Eq (ProdInsertIdx.eq.Prod s d).symm, ProdInsertIdx.eq.Prod]
  change ((List.replicate (s.prod / s.prod) X.data).map List.Vector.toList).flatten = X.data.val
  rw [List.map_replicate]
  if h : s.prod = 0 then
    have h_nil : X.data.val = [] := List.length_eq_zero_iff.mp (X.data.property.trans h)
    simp [h, h_nil]
  else
    simp [Nat.div_self (Nat.pos_of_ne_zero h)]
    rfl


-- created on 2026-07-10
-- updated on 2026-11-20
