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

/-- Key identity: W² = I. Follows from the Walsh-Hadamard inversion formula:
    Σ_{z ∈ {0,1}^n} (-1)^{z·(x⊕y)} = 2^n · 𝟙[x = y].
    Goal state:  W n * W n = 1 -/
lemma W_mul_W (n : ℕ) : W n * W n = 1 := by
  sorry

/-! ## Symmetry of Hamiltonians -/

/-- H_c is Hermitian (diagonal real matrix). -/
lemma Hc_isHermitian (n : ℕ) (c : PseudoBool n) : (Hc n c).IsHermitian := by
  rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [Hc, Matrix.diagonal_transpose]

/-- H_b is Hermitian: (W·diag(b)·W)ᴴ = W·diag(b)·W.
    Proof: uses W is Hermitian and diag(b) is Hermitian.
    Goal state:  (Hb n b).conjTranspose = Hb n b -/
lemma Hb_isHermitian (n : ℕ) (b : PseudoBool n) : (Hb n b).IsHermitian := by
  sorry

/-- H(t) is Hermitian for all t ∈ ℝ.
    Proof: sum of Hermitian matrices scaled by real scalars is Hermitian.
    Goal state:  (Hint n b c t).conjTranspose = Hint n b c t -/
lemma Hint_isHermitian (n : ℕ) (b c : PseudoBool n) (t : ℝ) :
    (Hint n b c t).IsHermitian := by
  sorry

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
