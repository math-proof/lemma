import Instance.EllipticCurve_FunctionFieldPullback

namespace WeierstrassCurve.Affine

section WeilPairingDefs

variable {R : Type*} [Field R] (W : WeierstrassCurve R) (K : Type*) [Field K] [Algebra R K]
  [DecidableEq K]

open Classical in

noncomputable def placeIdeal (P : (W⁄K).Point) : Ideal (W⁄K).CoordinateRing :=
  if hP : P = 0 then ⊤ else (placeOf W K P hP).asIdeal


def fibSet (n : ℤ) (Q : (W⁄K).Point) : Set (W⁄K).Point := {P | n • P = Q}


noncomputable def fibIdeal (n : ℤ) (Q : (W⁄K).Point) : Ideal (W⁄K).CoordinateRing :=
  if h : (fibSet W K n Q).Finite then ∏ P ∈ h.toFinset, placeIdeal W K P else ⊤


noncomputable def weilNum (n : ℤ) (T : (W⁄K).Point) : (W⁄K).CoordinateRing :=
  if h : (fibIdeal W K n T).IsPrincipal then @Submodule.IsPrincipal.generator _ _ _ _ _ _ h else 1


noncomputable def weilFun (n : ℤ) (T : (W⁄K).Point) : (W⁄K).FunctionField :=
  algebraMap _ (W⁄K).FunctionField (weilNum W K n T) / algebraMap _ (W⁄K).FunctionField (weilNum W K n 0)

open Classical in

noncomputable def weilPairing0 [IsAlgClosed K] [W.IsElliptic] (n : ℤ) (S T : (W⁄K).Point) : Kˣ :=
  if h : ∃ c : Kˣ, transEquiv W K S (weilFun W K n T) =
      algebraMap K (W⁄K).FunctionField (c : K) * weilFun W K n T
  then h.choose else 1


end WeilPairingDefs

end WeierstrassCurve.Affine
