/- https://github.com/facebookresearch/atlas-lean/blob/main/Atlas/FC/OpenQuantumProblem35_ame_9_10_open_solution.lean -/

/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/


import Mathlib


open scoped BigOperators

namespace OpenQuantumProblem35


abbrev Config (n d : ℕ) := Fin n → Fin d


abbrev StateVector (n d : ℕ) := EuclideanSpace ℂ (Config n d)


abbrev mkStateVector {n d : ℕ} (ψ : Config n d → ℂ) : StateVector n d :=
  WithLp.toLp 2 ψ


instance {n d : ℕ} : CoeFun (StateVector n d) (fun _ => Config n d → ℂ) where
  coe ψ := ψ.ofLp


def IsNormalized {n d : ℕ} (ψ : StateVector n d) : Prop :=
  ‖ψ‖ = 1


def permuteConfig {n d : ℕ} (π : Equiv.Perm (Fin n)) (x : Config n d) : Config n d :=
  fun i => x (π i)


def permuteState {n d : ℕ} (π : Equiv.Perm (Fin n)) (ψ : StateVector n d) : StateVector n d :=
  mkStateVector fun x => ψ (permuteConfig π x)


def combineFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (x : Config m d) (y : Config (n - m) d) : Config n d :=
  fun i =>
    if hi : i.1 < m then
      x ⟨i.1, hi⟩
    else
      y ⟨i.1 - m, by
        have him : m ≤ i.1 := Nat.le_of_not_gt hi
        omega⟩


noncomputable def reducedDensityFirst {n d : ℕ} (m : ℕ) (hm : m ≤ n) (ψ : StateVector n d) :
    Matrix (Config m d) (Config m d) ℂ :=
  fun x y =>
    ∑ z : Config (n - m) d,
      ψ (combineFirst (n := n) (d := d) m hm x z) *
        star (ψ (combineFirst (n := n) (d := d) m hm y z))


noncomputable def maximallyMixed (m d : ℕ) :
    Matrix (Config m d) (Config m d) ℂ :=
  ((Fintype.card (Config m d) : ℂ)⁻¹) •
    (1 : Matrix (Config m d) (Config m d) ℂ)


def HasMaximallyMixedFirstReduction {n d : ℕ} (m : ℕ) (hm : m ≤ n)
    (ψ : StateVector n d) : Prop :=
  reducedDensityFirst (n := n) (d := d) m hm ψ = maximallyMixed m d


def IsAME {n d : ℕ} (ψ : StateVector n d) : Prop :=
  IsNormalized ψ ∧
    ∀ π : Equiv.Perm (Fin n),
      HasMaximallyMixedFirstReduction (n := n) (d := d)
        (n / 2) (Nat.div_le_self n 2) (permuteState π ψ)


def ExistsAME (n d : ℕ) : Prop :=
  ∃ ψ : StateVector n d, IsAME (n := n) (d := d) ψ


def IsConstantConfig {n d : ℕ} (x : Config n d) : Prop :=
  ∀ i j, x i = x j

instance {n d : ℕ} : DecidablePred (@IsConstantConfig n d) := by
  intro x
  unfold IsConstantConfig
  infer_instance


def q5Graph (i j : Fin 10) : ZMod 5 :=
  let e := Nat.dist i.1 j.1
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0


def q5CutMatrix (A : Finset (Fin 10)) (hA : A.card = 5) :
    Matrix (Fin 5) (Fin 5) (ZMod 5) :=
  let hAc : Aᶜ.card = 5 := by simp [Finset.card_compl, hA]
  fun i j => q5Graph ((Aᶜ.orderIsoOfFin hAc) i).1 ((A.orderIsoOfFin hA) j).1


def q5Indices (mask : Fin 10 → Bool) (b : Bool) : List (Fin 10) :=
  (List.finRange 10).filter (fun i => mask i == b)

def q5Select (mask : Fin 10 → Bool) (b : Bool) (k : Fin 5) : ℕ :=
  ((q5Indices mask b)[k.1]?.getD 0).1

def q5GraphNat (i j : ℕ) : ℕ :=
  let e := Nat.dist i j
  let e := min e (10 - e)
  if e = 1 then 3 else if e = 2 ∨ e = 3 then 1 else 0

def q5MaskMatrix (mask : Fin 10 → Bool) : Matrix (Fin 5) (Fin 5) ℤ :=
  fun i j => q5GraphNat (q5Select mask false i) (q5Select mask true j)

set_option maxHeartbeats 0
set_option maxRecDepth 100000

def detFinThreeInt (M : Matrix (Fin 3) (Fin 3) ℤ) : ℤ :=
  M 0 0 * M 1 1 * M 2 2 + M 0 1 * M 1 2 * M 2 0 +
  M 0 2 * M 1 0 * M 2 1 - M 0 2 * M 1 1 * M 2 0 -
  M 0 1 * M 1 0 * M 2 2 - M 0 0 * M 1 2 * M 2 1

def detFinFourInt (M : Matrix (Fin 4) (Fin 4) ℤ) : ℤ :=
  ∑ j : Fin 4, (-1) ^ (j : ℕ) * M 0 j *
    detFinThreeInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

def detFinFiveInt (M : Matrix (Fin 5) (Fin 5) ℤ) : ℤ :=
  ∑ j : Fin 5, (-1) ^ (j : ℕ) * M 0 j *
    detFinFourInt (M.submatrix (Fin.succAbove 0) (Fin.succAbove j))

def q5Affine (s : Fin 10) (flip : Bool) : Equiv.Perm (Fin 10) :=
  if flip then (Equiv.neg (Fin 10)).trans (Equiv.addLeft s) else Equiv.addLeft s


def q5Representatives : List (Finset (Fin 10)) :=
  [ {0, 1, 2, 3, 4}, {0, 1, 2, 3, 5}, {0, 1, 2, 4, 5},
    {0, 1, 2, 3, 6}, {0, 1, 2, 4, 6}, {0, 1, 3, 4, 6},
    {0, 2, 3, 4, 6}, {0, 1, 2, 5, 6}, {0, 1, 3, 5, 6},
    {0, 1, 2, 4, 7}, {0, 1, 3, 4, 7}, {0, 1, 2, 5, 7},
    {0, 1, 3, 5, 7}, {0, 2, 3, 5, 7}, {0, 1, 4, 5, 7},
    {0, 2, 4, 6, 8} ]

def finsetMapEquiv {α β : Type*} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (S : Finset α) : S ≃ S.map e.toEmbedding where
  toFun x := ⟨e x, by simp⟩
  invFun y := ⟨e.symm y.1, by
    simpa only [Finset.mem_map_equiv] using y.2⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp

def finsetMapComplEquiv {α : Type*} [Fintype α] [DecidableEq α]
    (e : Equiv.Perm α) (S : Finset α) :
    ↥(Sᶜ) ≃ ↥((S.map e.toEmbedding)ᶜ) where
  toFun x := ⟨e x.1, by
    simp only [Finset.mem_compl, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    simpa only [Finset.mem_compl] using x.2⟩
  invFun y := ⟨e.symm y.1, by
    simp only [Finset.mem_compl]
    have hy := y.2
    simpa only [Finset.mem_compl, Finset.mem_map_equiv] using hy⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp


def q2Cycle (i j : Fin 9) : ZMod 2 :=
  if Nat.dist i.1 j.1 = 1 ∨ Nat.dist i.1 j.1 = 8 then 1 else 0


def q2Check₁ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 1 + x 3 + x 4 + x 6 + x 7

def q2Check₂ (x : Fin 9 → ZMod 2) : ZMod 2 :=
  x 0 + x 2 + x 3 + x 5 + x 6 + x 8


def localTenEquiv : Fin 2 × Fin 5 ≃ Fin 10 := finProdFinEquiv

def bitPart (x : Fin 10) : ZMod 2 := (localTenEquiv.symm x).1

def quintPart (x : Fin 10) : ZMod 5 := (localTenEquiv.symm x).2


def localPartsEquiv : Fin 10 ≃ ZMod 2 × ZMod 5 :=
  localTenEquiv.symm.trans
    (Equiv.prodCongr (ZMod.finEquiv 2).toEquiv (ZMod.finEquiv 5).toEquiv)

@[simp] lemma localPartsEquiv_apply (x : Fin 10) :
    localPartsEquiv x = (bitPart x, quintPart x) := rfl


def graphPhase {n p : ℕ} (G : Fin n → Fin n → ZMod p)
    (x : Fin n → ZMod p) : ZMod p :=
  ∑ i : Fin n, ∑ j ∈ Finset.univ.filter (fun j : Fin n => i.1 < j.1),
    G i j * x i * x j

def q2Label (a : Fin 2 → ZMod 2) (i : Fin 9) : ZMod 2 :=
  a 0 * (if i.1 ∈ ([0, 1, 3, 4, 6, 7] : List ℕ) then 1 else 0) +
  a 1 * (if i.1 ∈ ([0, 2, 3, 5, 6, 8] : List ℕ) then 1 else 0)

set_option maxRecDepth 10000 in

def q5Logical (a : Fin 2 → ZMod 2) : ZMod 5 :=
  ((a 0).val + 2 * (a 1).val : ℕ)

def binaryPhase (a : Fin 2 → ZMod 2) (u : Fin 9 → ZMod 2) : ZMod 2 :=
  graphPhase q2Cycle u + ∑ i, q2Label a i * u i

def quinaryWord (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : Fin 10 → ZMod 5
  | ⟨0, _⟩ => q5Logical a
  | ⟨i + 1, h⟩ => v ⟨i, by omega⟩

@[simp] lemma quinaryWord_zero (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) :
    quinaryWord a v 0 = q5Logical a := rfl

@[simp] lemma quinaryWord_succ (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5)
    (i : Fin 9) : quinaryWord a v (Fin.succ i) = v i := by
  rfl

def quinaryPhase (a : Fin 2 → ZMod 2) (v : Fin 9 → ZMod 5) : ZMod 5 :=
  graphPhase q5Graph (quinaryWord a v)

noncomputable def ameAmplitude (x : Config 9 10) : ℂ :=
  let u : Fin 9 → ZMod 2 := fun i => bitPart (x i)
  let v : Fin 9 → ZMod 5 := fun i => quintPart (x i)
  ((Real.sqrt (2 ^ 11 * 5 ^ 9 : ℝ) : ℂ)⁻¹) *
    ∑ a : Fin 2 → ZMod 2,
      ZMod.stdAddChar (binaryPhase a u) * ZMod.stdAddChar (quinaryPhase a v)

noncomputable def ameState : StateVector 9 10 := mkStateVector ameAmplitude

def ame_9_10_open_statement : Prop := ExistsAME 9 10

def pasteOn {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) : ι → R :=
  fun i => if hi : i ∈ A then x ⟨i, hi⟩ else z ⟨i, hi⟩

@[simp] lemma pasteOn_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : A) :
    pasteOn A x z i.1 = x i := by simp [pasteOn, i.2]

@[simp] lemma pasteOn_not_mem {ι R : Type*} [DecidableEq ι] (A : Finset ι)
    (x : A → R) (z : {i : ι // i ∉ A} → R) (i : {i : ι // i ∉ A}) :
    pasteOn A x z i.1 = z i := by simp [pasteOn, i.2]

def liftPhysicalSet (A : Finset (Fin 9)) : Finset (Fin 10) :=
  {0} ∪ A.map ⟨Fin.succ, Fin.succ_injective 9⟩

@[simp] lemma liftPhysicalSet_card (A : Finset (Fin 9)) :
    (liftPhysicalSet A).card = A.card + 1 := by
  rw [liftPhysicalSet, Finset.card_union_of_disjoint]
  · simp
    omega
  · simp [Finset.disjoint_left]

@[simp] lemma liftPhysicalSet_zero (A : Finset (Fin 9)) :
    (0 : Fin 10) ∈ liftPhysicalSet A := by simp [liftPhysicalSet]

@[simp] lemma liftPhysicalSet_succ (A : Finset (Fin 9)) (i : Fin 9) :
    Fin.succ i ∈ liftPhysicalSet A ↔ i ∈ A := by
  simp [liftPhysicalSet]

def splitFunctionsEquiv (ι : Type*) :
    (ι → Fin 10) ≃ (ι → ZMod 2) × (ι → ZMod 5) where
  toFun z := (fun i => bitPart (z i), fun i => quintPart (z i))
  invFun z := fun i => localPartsEquiv.symm (z.1 i, z.2 i)
  left_inv z := by
    funext i
    exact localPartsEquiv.symm_apply_apply (z i)
  right_inv z := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))
    · funext i
      exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (z.1 i, z.2 i))

@[simp] lemma bitPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    bitPart (localPartsEquiv.symm (u, v)) = u := by
  exact congrArg Prod.fst (localPartsEquiv.apply_symm_apply (u, v))

@[simp] lemma quintPart_localPartsEquiv_symm (u : ZMod 2) (v : ZMod 5) :
    quintPart (localPartsEquiv.symm (u, v)) = v := by
  exact congrArg Prod.snd (localPartsEquiv.apply_symm_apply (u, v))

def splitOnEquiv {ι R : Type*} [DecidableEq ι] (A : Finset ι) :
    ((A → R) × ({i : ι // i ∉ A} → R)) ≃ (ι → R) where
  toFun p := pasteOn A p.1 p.2
  invFun f := (fun i => f i.1, fun i => f i.1)
  left_inv p := by
    apply Prod.ext <;> funext i
    · exact pasteOn_mem A p.1 p.2 i
    · exact pasteOn_not_mem A p.1 p.2 i
  right_inv f := by
    funext i
    by_cases hi : i ∈ A <;> simp [pasteOn, hi]

def permFirstSet (π : Equiv.Perm (Fin 9)) : Finset (Fin 9) :=
  Finset.univ.filter (fun i => (π i).1 < 4)

@[simp] lemma permFirstSet_mem (π : Equiv.Perm (Fin 9)) (i : Fin 9) :
    i ∈ permFirstSet π ↔ (π i).1 < 4 := by simp [permFirstSet]

def permFrontEquiv (π : Equiv.Perm (Fin 9)) : permFirstSet π ≃ Fin 4 where
  toFun i := ⟨(π i.1).1, (permFirstSet_mem π i.1).mp i.2⟩
  invFun k := ⟨π.symm ⟨k.1, by omega⟩, by simp⟩
  left_inv i := by ext; simp
  right_inv k := by ext; simp

def permRestEquiv (π : Equiv.Perm (Fin 9)) :
    {i : Fin 9 // i ∉ permFirstSet π} ≃ Fin 5 where
  toFun i := ⟨(π i.1).1 - 4, by
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    have hu : (π i.1).1 < 9 := (π i.1).2
    omega⟩
  invFun k := ⟨π.symm ⟨k.1 + 4, by omega⟩, by
    simp only [permFirstSet_mem, Equiv.apply_symm_apply]
    omega⟩
  left_inv i := by
    apply Subtype.ext
    apply π.injective
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    have hn : ¬ (π i.1).1 < 4 := by simpa [permFirstSet] using i.2
    omega
  right_inv k := by
    apply Fin.ext
    simp only [Equiv.apply_symm_apply]
    omega
