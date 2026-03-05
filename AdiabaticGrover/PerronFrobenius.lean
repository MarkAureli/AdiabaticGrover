import AdiabaticGrover.Basic

/-!
# Perron-Frobenius Theorem (Axiomatized)

The classical Perron-Frobenius theorem states that an irreducible non-negative matrix
has a simple largest eigenvalue with a positive eigenvector.

For stoquastic Hamiltonians we need the version for real symmetric matrices with
strictly negative off-diagonal entries: such a matrix is irreducible (after sign flip),
so its **minimum** eigenvalue is simple.

Reference: Perron (1907), Frobenius (1912); Horn & Johnson "Matrix Analysis" §8.3.

## Mathlib status
As of Mathlib v4.28.0, a general Perron-Frobenius theorem for matrices is not
available in Mathlib (there is `Mathlib.LinearAlgebra.Matrix.PosDef` for positive
definite matrices, but not irreducibility / spectral gap results). We axiomatize here.
-/

/-! ## Off-Diagonal Sign Condition -/

/-- A matrix has **strictly negative off-diagonal** entries if M i j < 0 for all i ≠ j.
    This is the matrix-level condition for stoquastic Hamiltonians H(t) with t ∈ (0,1). -/
def HasNegOffDiag {α : Type*} [DecidableEq α] [Fintype α]
    (M : Matrix α α ℝ) : Prop :=
  ∀ i j : α, i ≠ j → M i j < 0

/-! ## Perron-Frobenius Axiom -/

/-- **Perron-Frobenius** (axiomatized): A real symmetric matrix with strictly negative
    off-diagonal entries has a **simple** minimum eigenvalue — all other eigenvalues
    are strictly larger.

    The proof sketch: negating the off-diagonal sign gives a non-negative irreducible
    matrix; classical PF gives a simple maximum eigenvalue for that matrix; translating
    back gives a simple minimum for the original.

    Reference: Perron (1907), Frobenius (1912); Horn & Johnson §8.3. -/
axiom perron_frobenius {n : ℕ} [Nonempty (BoolVec n)]
    (M : Matrix (BoolVec n) (BoolVec n) ℝ)
    (hM : M.IsHermitian)
    (hoff : HasNegOffDiag M) :
    ∃ μ_min : ℝ,
      IsEigenvalue M μ_min ∧
      ∀ μ, IsEigenvalue M μ → μ = μ_min ∨ μ > μ_min
