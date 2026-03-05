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

/-! ## Stoquasticity -/

/-- A pseudo-Boolean function b is **stoquastic** if its (unnormalized) Walsh-Hadamard
    transform is non-positive at all non-zero frequencies:
      B̂(k) = ∑_z b(z) * (-1)^{bitDot k z} ≤ 0  for all k ≠ 0.
    This ensures H_b has non-positive off-diagonal entries (in the standard basis). -/
def IsStoquastic (n : ℕ) (b : PseudoBool n) : Prop :=
  ∀ k : BoolVec n, k ≠ 0 → ∑ z : BoolVec n, b z * (-1 : ℝ) ^ bitDot n k z ≤ 0

/-! ## Matrix Entry Formula for H_b -/

/-- Sign identity: (-1)^{x·z} · (-1)^{z·y} = (-1)^{(x⊕y)·z}.
    Proof: factor both sides as products over coordinates; for each bit,
    the parity of x_i*z_i + z_i*y_i equals (x_i ⊕ y_i)*z_i (8 Boolean cases). -/
private lemma neg1_pow_bitDot_xor (n : ℕ) (x y z : BoolVec n) :
    (-1 : ℝ) ^ bitDot n x z * (-1) ^ bitDot n z y =
    (-1) ^ bitDot n (fun i => xor (x i) (y i)) z := by
  simp only [bitDot_pow_neg1_prod, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  simp only [← pow_add]
  -- For each bit: parity of x_i*z_i + z_i*y_i equals (x_i ⊕ y_i)*z_i (8 Bool cases).
  -- Can't use decide/native_decide: ℝ uses Classical.propDecidable. Case split manually.
  rcases Bool.eq_false_or_eq_true (x i) with hx | hx <;>
  rcases Bool.eq_false_or_eq_true (y i) with hy | hy <;>
  rcases Bool.eq_false_or_eq_true (z i) with hz | hz <;>
  simp [hx, hy, hz]

/-- Matrix entry formula for H_b:
      (Hb n b) x y = (∑_z b(z) · (-1)^{(x⊕y)·z}) / 2^n
    Proof: unfold W, simplify diagonal matrix product, collect √(2^n)² = 2^n,
    apply `neg1_pow_bitDot_xor`. -/
theorem Hb_entry (n : ℕ) (b : PseudoBool n) (x y : BoolVec n) :
    (Hb n b) x y =
    (∑ z : BoolVec n, b z * (-1 : ℝ) ^ bitDot n (fun i => xor (x i) (y i)) z) / 2 ^ n := by
  simp only [Hb, Matrix.mul_apply, Matrix.diagonal_apply, mul_ite, mul_zero,
             Finset.sum_ite_eq', Finset.mem_univ, if_true, W, Matrix.of_apply, whtEntry]
  -- Goal: ∑ z, (-1)^(bitDot n x z) / √(2^n) * b z * ((-1)^(bitDot n z y) / √(2^n))
  --     = (∑ z, b z * (-1)^(bitDot n (x⊕y) z)) / 2^n
  have sqrt_sq : Real.sqrt ((2 : ℝ) ^ n) * Real.sqrt ((2 : ℝ) ^ n) = (2 : ℝ) ^ n :=
    Real.mul_self_sqrt (by positivity)
  -- Step 1: rewrite each summand as b z * (-1)^p * (-1)^q / 2^n (field identity after sqrt_sq)
  conv_lhs =>
    arg 2; ext z
    rw [show (-1 : ℝ) ^ bitDot n x z / Real.sqrt ((2 : ℝ) ^ n) * b z *
            ((-1) ^ bitDot n z y / Real.sqrt ((2 : ℝ) ^ n)) =
          b z * ((-1 : ℝ) ^ bitDot n x z * (-1) ^ bitDot n z y) / (2 : ℝ) ^ n by
      rw [div_mul_eq_mul_div, div_mul_div_comm, sqrt_sq]; ring]
  -- Step 2: pull common denominator 2^n out of the sum
  rw [← Finset.sum_div]
  congr 1
  -- Step 3: apply neg1_pow_bitDot_xor to match the (-1)^(bitDot n (x⊕y) z) form
  apply Finset.sum_congr rfl; intro z _
  rw [neg1_pow_bitDot_xor]

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
  simp only [IsEigenvalue, IsEigenpair, Hc]
  constructor
  · rintro ⟨v, hv, heq⟩
    obtain ⟨x, hx⟩ : ∃ x, v x ≠ 0 :=
      not_forall.mp (fun h => hv (funext h))
    exact ⟨x, mul_right_cancel₀ hx (by
      have := congr_fun heq x
      simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
      linarith)⟩
  · rintro ⟨x, rfl⟩
    refine ⟨Pi.single x 1, Pi.single_ne_zero_iff.mpr one_ne_zero, ?_⟩
    simp [← Pi.single_smul', smul_eq_mul]

/-- Eigenvalues of H_b are exactly the values of b.
    Proof: H_b ~ diag(b) via W (using W² = I), so same spectrum.
    Goal state:  IsEigenvalue (Hb n b) μ ↔ ∃ x : BoolVec n, b x = μ -/
lemma Hb_eigenvalues (n : ℕ) (b : PseudoBool n) (μ : ℝ) :
    IsEigenvalue (Hb n b) μ ↔ ∃ x : BoolVec n, b x = μ := by
  rw [← Hc_eigenvalues]
  simp only [IsEigenvalue, IsEigenpair, Hb, Hc]
  -- W is its own inverse (W² = I), so v ↦ W·v bijects eigenpairs of Hb ↔ eigenpairs of diag(b)
  have W_inv : ∀ v : BoolVec n → ℝ, (W n).mulVec ((W n).mulVec v) = v := fun v => by
    rw [Matrix.mulVec_mulVec, W_mul_W, Matrix.one_mulVec]
  have W_ne_zero : ∀ v : BoolVec n → ℝ, v ≠ 0 → (W n).mulVec v ≠ 0 := fun v hv hw => by
    exact hv (by rw [← W_inv v, hw, Matrix.mulVec_zero])
  constructor
  · rintro ⟨v, hv, heq⟩
    refine ⟨(W n).mulVec v, W_ne_zero v hv, ?_⟩
    -- Apply W on left: W·(W·diag(b)·W·v) = diag(b)·(W·v)
    have := congr_arg (W n).mulVec heq
    simp only [Matrix.mulVec_mulVec, Matrix.mulVec_smul] at this
    -- this : (W n * (W n * Matrix.diagonal b * W n)).mulVec v = μ • (W n).mulVec v
    rw [show W n * (W n * Matrix.diagonal b * W n) = Matrix.diagonal b * W n from by
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, W_mul_W, Matrix.one_mul],
      ← Matrix.mulVec_mulVec] at this
    exact this
  · rintro ⟨w, hw, heq⟩
    refine ⟨(W n).mulVec w, W_ne_zero w hw, ?_⟩
    -- W·diag(b)·W·(W·w) = W·diag(b)·w = W·(μ·w) = μ·(W·w)
    simp only [Matrix.mulVec_mulVec]
    rw [show W n * Matrix.diagonal b * W n * W n = W n * Matrix.diagonal b from by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, W_mul_W, Matrix.mul_one]]
    rw [← Matrix.mulVec_mulVec, heq, Matrix.mulVec_smul]
