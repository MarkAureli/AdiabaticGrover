import Mathlib

/-!
# Adiabatic Grover: Core Definitions

n-qubit interpolating Hamiltonian H(t) = (1-t)·H_b + t·H_c, where
- H_c = diag(c) is diagonal in the standard basis
- H_b = W·diag(b)·W is H_c conjugated by the n-fold Hadamard W

State space is indexed by `BoolVec n = Fin n → Bool`, representing {0,1}^n.
-/

/-! ## Type Aliases -/

/-- A point in {0,1}^n, represented as a function Fin n → Bool. -/
abbrev BoolVec (n : ℕ) := Fin n → Bool

/-- A pseudo-Boolean function b : {0,1}^n → ℝ. -/
abbrev PseudoBool (n : ℕ) := BoolVec n → ℝ

/-! ## Walsh-Hadamard Transform -/

/-- The inner product x · y = Σ_i (x_i ∧ y_i), as a natural number. -/
def bitDot (n : ℕ) (x y : BoolVec n) : ℕ :=
  ∑ i : Fin n, (x i && y i).toNat

/-- Entry of the normalized n-fold Walsh-Hadamard matrix:
    W_{xy} = (-1)^{x·y} / √(2^n) -/
noncomputable def whtEntry (n : ℕ) (x y : BoolVec n) : ℝ :=
  (-1 : ℝ) ^ bitDot n x y / Real.sqrt ((2 : ℝ) ^ n)

/-- The n-fold Walsh-Hadamard transform matrix W:
    W_{xy} = (-1)^{x·y} / √(2^n). Satisfies W² = I (it is its own inverse). -/
noncomputable def W (n : ℕ) : Matrix (BoolVec n) (BoolVec n) ℝ :=
  Matrix.of (whtEntry n)

/-! ## Hamiltonians -/

/-- Target (problem) Hamiltonian: H_c = diag(c), diagonal in the standard basis.
    Eigenvalues are {c(x) : x ∈ {0,1}^n}. -/
noncomputable def Hc (n : ℕ) (c : PseudoBool n) : Matrix (BoolVec n) (BoolVec n) ℝ :=
  Matrix.diagonal c

/-- Initial (driver) Hamiltonian: H_b = W · diag(b) · W.
    Unitarily equivalent to diag(b), so eigenvalues are {b(x) : x ∈ {0,1}^n}. -/
noncomputable def Hb (n : ℕ) (b : PseudoBool n) : Matrix (BoolVec n) (BoolVec n) ℝ :=
  W n * Matrix.diagonal b * W n

/-- Interpolating Hamiltonian: H(t) = (1-t)·H_b + t·H_c.
    Linear (hence analytic) family of real symmetric matrices, t ∈ [0,1]. -/
noncomputable def Hint (n : ℕ) (b c : PseudoBool n) (t : ℝ) :
    Matrix (BoolVec n) (BoolVec n) ℝ :=
  (1 - t) • Hb n b + t • Hc n c

/-! ## Basic Properties of W -/

/-- bitDot is symmetric: x · y = y · x. -/
lemma bitDot_comm (n : ℕ) (x y : BoolVec n) : bitDot n x y = bitDot n y x := by
  simp [bitDot, Bool.and_comm]

/-- WHT entry is symmetric in its two indices: W_{xy} = W_{yx}. -/
lemma whtEntry_symm (n : ℕ) (x y : BoolVec n) : whtEntry n x y = whtEntry n y x := by
  simp [whtEntry, bitDot_comm]

/-- W is a symmetric matrix: W = Wᵀ, stated as `Matrix.IsSymm`. -/
lemma W_isSymm (n : ℕ) : (W n).IsSymm := by
  unfold Matrix.IsSymm
  ext x y
  simp [Matrix.transpose_apply, W, Matrix.of_apply, whtEntry_symm]

/-- W is Hermitian (self-adjoint over ℝ): Wᴴ = W.
    Follows from W being real and symmetric. -/
lemma W_isHermitian (n : ℕ) : (W n).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  exact W_isSymm n

/-! ### Helpers for W² = I -/

/-- (-1)^{x·z} factors as a product over coordinates. -/
private lemma bitDot_pow_neg1_prod (n : ℕ) (x z : BoolVec n) :
    (-1 : ℝ) ^ bitDot n x z = ∏ i : Fin n, (-1 : ℝ) ^ ((x i && z i).toNat) := by
  simp [bitDot, ← Finset.prod_pow_eq_pow_sum]

/-- For each bit position, summing over b ∈ Bool gives 2 if xi = yi, else 0. -/
private lemma bool_wht_factor (xi yi : Bool) :
    ∑ b : Bool, ((-1 : ℝ) ^ ((xi && b).toNat) * (-1) ^ ((b && yi).toNat)) =
    if xi = yi then 2 else 0 := by
  fin_cases xi <;> fin_cases yi <;>
    simp [Bool.false_and, Bool.and_false, Bool.true_and, Bool.and_true,
          show (1 : ℝ) + 1 = 2 from by norm_num]

/-- Walsh-Hadamard orthogonality: Σ_z (-1)^{x·z} · (-1)^{z·y} = 2^n · [x=y]. -/
private lemma wht_orthogonality (n : ℕ) (x y : BoolVec n) :
    ∑ z : BoolVec n, (-1 : ℝ) ^ bitDot n x z * (-1) ^ bitDot n z y =
    if x = y then (2 : ℝ) ^ n else 0 := by
  simp_rw [bitDot_pow_neg1_prod, ← Finset.prod_mul_distrib]
  rw [(Fintype.prod_sum (fun i (b : Bool) =>
        (-1 : ℝ) ^ ((x i && b).toNat) * (-1) ^ ((b && y i).toNat))).symm]
  simp_rw [bool_wht_factor]
  by_cases hxy : x = y
  · subst hxy; simp [Finset.prod_const, Fintype.card_fin]
  · simp only [hxy, ↓reduceIte]
    have ⟨i, hi⟩ : ∃ i, x i ≠ y i := Function.ne_iff.mp hxy
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi])

/-- Key identity: W² = I (Walsh-Hadamard matrix is its own inverse). -/
lemma W_mul_W (n : ℕ) : W n * W n = 1 := by
  ext x y
  simp only [Matrix.mul_apply, W, Matrix.of_apply, whtEntry, Matrix.one_apply]
  rw [show ∑ z : BoolVec n, (-1 : ℝ) ^ bitDot n x z / Real.sqrt (2 ^ n) *
          ((-1) ^ bitDot n z y / Real.sqrt (2 ^ n)) =
        (∑ z : BoolVec n, (-1 : ℝ) ^ bitDot n x z * (-1) ^ bitDot n z y) / (2 : ℝ) ^ n
      from by simp_rw [div_mul_div_comm, ← Finset.sum_div,
                        Real.mul_self_sqrt (by positivity : (0:ℝ) ≤ 2^n)]]
  rw [wht_orthogonality]
  split_ifs with h
  · exact div_self (by positivity)
  · exact zero_div _

/-! ## Symmetry of Hamiltonians -/

/-- H_c is Hermitian (diagonal real matrix). -/
lemma Hc_isHermitian (n : ℕ) (c : PseudoBool n) : (Hc n c).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [Hc, Matrix.diagonal_transpose]

/-- H_b is Hermitian: (W·diag(b)·W)ᴴ = W·diag(b)·W.
    Proof: W is Hermitian so W = Wᴴ; then Wᴴ·diag(b)·W is Hermitian by
    `isHermitian_conjTranspose_mul_mul`. -/
lemma Hb_isHermitian (n : ℕ) (b : PseudoBool n) : (Hb n b).IsHermitian := by
  unfold Hb
  nth_rw 1 [← W_isHermitian n]
  exact Matrix.isHermitian_conjTranspose_mul_mul (W n) (Hc_isHermitian n b)

/-- H(t) is Hermitian for all t ∈ ℝ.
    Proof: sum of Hermitian matrices scaled by real scalars is Hermitian. -/
lemma Hint_isHermitian (n : ℕ) (b c : PseudoBool n) (t : ℝ) :
    (Hint n b c t).IsHermitian := by
  unfold Hint
  apply Matrix.IsHermitian.add
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (Hb_isHermitian n b).eq]
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_smul, star_trivial, (Hc_isHermitian n c).eq]

/-! ## Eigenvalue Definitions -/

/-- μ is an eigenvalue of M with eigenvector v (over index type BoolVec n). -/
def IsEigenpair {n : ℕ} (M : Matrix (BoolVec n) (BoolVec n) ℝ) (μ : ℝ)
    (v : BoolVec n → ℝ) : Prop :=
  v ≠ 0 ∧ M.mulVec v = μ • v

/-- μ is an eigenvalue of M. -/
def IsEigenvalue {n : ℕ} (M : Matrix (BoolVec n) (BoolVec n) ℝ) (μ : ℝ) : Prop :=
  ∃ v, IsEigenpair M μ v

/-- Eigenvalues of H_c are exactly the values of c.
    Proof: H_c = diag(c), standard basis vectors are eigenvectors.
    Goal state:  IsEigenvalue (Hc n c) μ ↔ ∃ x : BoolVec n, c x = μ -/
lemma Hc_eigenvalues (n : ℕ) (c : PseudoBool n) (μ : ℝ) :
    IsEigenvalue (Hc n c) μ ↔ ∃ x : BoolVec n, c x = μ := by
  sorry

/-- Eigenvalues of H_b are exactly the values of b.
    Proof: H_b ~ diag(b) via W (using W² = I), so same spectrum.
    Goal state:  IsEigenvalue (Hb n b) μ ↔ ∃ x : BoolVec n, b x = μ -/
lemma Hb_eigenvalues (n : ℕ) (b : PseudoBool n) (μ : ℝ) :
    IsEigenvalue (Hb n b) μ ↔ ∃ x : BoolVec n, b x = μ := by
  sorry
