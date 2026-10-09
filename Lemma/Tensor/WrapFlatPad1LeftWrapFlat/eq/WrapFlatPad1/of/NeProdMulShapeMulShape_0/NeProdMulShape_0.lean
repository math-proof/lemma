import sympy.core.mul
import sympy.Basic
import Lemma.List.LengthZipWithLcm.eq.Length.of.EqLengthS
import Lemma.Tensor.Pad1ZipWithLcmPad1.eq.ZipWithLcmPad1.of.Le.LeMaxLength
import Lemma.Tensor.WrapFlatPad1Pad1.eq.WrapFlatPad1.of.EqLength.Le.Le_Length
import Lemma.Tensor.WrapFlatWrapFlat.eq.WrapFlat.of.NeProd_0.Forall₂Dvd.Forall₂Dvd
import Lemma.List.Forall₂DvdLeft_ZipWithLcm.of.EqLengthS
open List Tensor


/--
Wrapping `A` through `A.mul B`, then through `(A.mul B).mul C`,
is wrapping `A` directly into the ternary output.
-/
@[path]
private lemma main
-- given
  (s s' s'' : List ℕ)
  (i : ℕ)
  (hAB : (mul_shape s s').prod ≠ 0)
  (_ : (mul_shape (mul_shape s s') s'').prod ≠ 0) :
-- imply
  wrapFlat (pad1 s (s.length ⊔ s'.length)) (mul_shape s s')
      (wrapFlat
        (pad1 (mul_shape s s')
          ((mul_shape s s').length ⊔ s''.length))
        (mul_shape (mul_shape s s') s'') i) =
      wrapFlat (pad1 s (s.length ⊔ s'.length ⊔ s''.length))
        (mul_shape (mul_shape s s') s'') i := by
-- proof
  let r := s.length ⊔ s'.length ⊔ s''.length
  let n := s.length ⊔ s'.length
  have hn : n ≤ r := le_sup_left
  have hABlen : (mul_shape s s').length = n := mul_shape_length s s'
  have hpadn : (mul_shape s s').length ⊔ s''.length = r := by
    rw [hABlen]
  have hmid :
      pad1 (mul_shape s s') r =
        (pad1 s r).zipWith Nat.lcm (pad1 s' r) := by
    rw [mul_shape_eq]
    exact Pad1ZipWithLcmPad1.eq.ZipWithLcmPad1.of.Le.LeMaxLength s s' le_rfl hn
  have hsm :
      List.Forall₂ (fun a b => a ∣ b) (pad1 s r)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r)) :=
    Forall₂DvdLeft_ZipWithLcm.of.EqLengthS _ _ (by
      rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])])
  have hmo :
      List.Forall₂ (fun a b => a ∣ b)
        ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
        (mul_shape (mul_shape s s') s'') := by
    have : mul_shape (mul_shape s s') s'' =
        (pad1 (mul_shape s s') r).zipWith Nat.lcm (pad1 s'' r) := by
      rw [mul_shape_eq, hpadn]
    rw [this, hmid]
    exact Forall₂DvdLeft_ZipWithLcm.of.EqLengthS _ _
      (by
        rw [LengthZipWithLcm.eq.Length.of.EqLengthS _ _
            (by rw [pad1_length s r (by simp [r]), pad1_length s' r (by simp [r])]),
          pad1_length s r (by simp [r]),
          pad1_length s'' r (by simp [r])])
  have hmid_ne : ((pad1 s r).zipWith Nat.lcm (pad1 s' r)).prod ≠ 0 := by
    rw [← hmid, pad1_prod]
    exact hAB
  have hcomp :=
    WrapFlatWrapFlat.eq.WrapFlat.of.NeProd_0.Forall₂Dvd.Forall₂Dvd (pad1 s r) ((pad1 s r).zipWith Nat.lcm (pad1 s' r))
      (mul_shape (mul_shape s s') s'') i hsm hmo hmid_ne
  have hpad :=
    WrapFlatPad1Pad1.eq.WrapFlatPad1.of.EqLength.Le.Le_Length s (mul_shape s s') le_sup_left hn hABlen
      (wrapFlat (pad1 (mul_shape s s')
          ((mul_shape s s').length ⊔ s''.length))
        (mul_shape (mul_shape s s') s'') i)
  rw [hpadn] at hpad ⊢
  rw [← hpad, hmid]
  exact hcomp


-- created on 2026-10-07
