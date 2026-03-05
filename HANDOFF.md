# HANDOFF.md — AdiabaticGrover

## Mathematical Setup

**Setting:** n-qubit quantum system with state space indexed by {0,1}^n ≅ Fin n → Bool.

**Objects:**
- `b, c : {0,1}^n → ℝ` — pseudo-Boolean functions
- `H_c = Σ_x c(x) |x⟩⟨x|` — target Hamiltonian (diagonal in standard basis)
- `H_b = W (Σ_x b(x) |x⟩⟨x|) W` — initial Hamiltonian (W = n-fold Hadamard)
- `H(t) = (1-t) H_b + t H_c` — interpolation Hamiltonian, t ∈ [0,1]

**Hadamard matrix:** W_{xy} = (-1)^{x·y} / √(2^n), where x·y = Σ_i x_i ∧ y_i.
Key property: W² = I (W is its own inverse), so H_b and diag(b) are unitarily equivalent.

**Eigenvalues:**
- λ_min(H_b) = min_{x} b(x)  (eigenvalues of H_b = eigenvalues of diag(b))
- λ_min(H_c) = min_{x} c(x)  (H_c is diagonal)

**Matrix elements of H(t)** (in standard basis):
```
H(t)_{x,y} = (1-t) · B̂(x ⊕ y) / 2^n + t · c(x) · δ_{x,y}
```
where B̂(k) = Σ_z b(z) (-1)^{k·z} is the (unnormalized) Walsh-Hadamard transform of b.

## Main Question

Find necessary and sufficient conditions on b and c such that there exists an
**analytic** function λ : [0,1] → ℝ with:
- λ(t) is an eigenvalue of H(t) for all t ∈ [0,1]
- λ(0) = min_{x} b(x)  (minimum eigenvalue of H_b)
- λ(1) = min_{x} c(x)  (minimum eigenvalue of H_c)

## Mathematical Observations

### Why "analytic" is non-trivial
The continuous version would be trivial: t ↦ λ_min(H(t)) is always continuous.
But λ_min(H(t)) need not be analytic — it has kinks wherever two eigenvalue
branches cross (exchange roles as the minimum).

H(t) = H_b + t(H_c − H_b) is a **degree-1 polynomial** (hence analytic) family
of real symmetric matrices.

By **Rellich's theorem** (1937), any real analytic family of self-adjoint operators
on a finite-dimensional space admits a global real analytic eigenvalue
parameterization: there exist analytic functions λ_1(t), ..., λ_N(t) (N = 2^n)
covering all eigenvalues for all t. Each Rellich branch at t=0 is rooted at some
eigenvalue of H_b, and at t=1 lands at some eigenvalue of H_c.

The question is: does the Rellich branch rooted at λ_min(H_b) land at λ_min(H_c)?

### Structure of the problem
- At t=0 the ground state has multiplicity = |argmin b| (number of minimizers of b).
- At t=1 the ground state has multiplicity = |argmin c|.
- Rellich branches can "exchange" when two branches collide (degeneracy point), so
  the branch starting at λ_min(H_b) may end above λ_min(H_c) even though
  the minimum of H(t) connects them continuously.

### Sufficient condition (spectral gap)
If λ_2(H(t)) > λ_1(H(t)) for all t ∈ [0,1] (spectral gap never closes), then
the ground state branch is analytic and non-degenerate throughout, so it
trivially connects the two ground states. But this is far from necessary.

### The Walsh-Hadamard structure
In the standard basis, H(t)_{x,y} = (1-t) B̂(x⊕y)/2^n + t c(x) δ_{x,y},
where B̂(k) = Σ_z b(z)(-1)^{k·z} (unnormalized WHT of b). The N&S conditions
on b and c are expected to be expressible in terms of this structure.

For the Grover case (b = 𝟙_{x≠0}, c = 𝟙_{x≠s}), the gap is Θ(1/√N).

## Implementation Plan

### Phase 1: Definitions (current)
- [x] `BoolVec n`, `PseudoBool n` type aliases
- [x] Walsh-Hadamard matrix `W n`
- [x] Hamiltonians `Hb`, `Hc`, `Hint`
- [ ] `W_mul_W : W n * W n = 1` (key identity, sorry for now)
- [ ] Symmetry lemmas for `Hb`, `Hc`, `Hint`

### Phase 2: Spectral Theory
- [ ] Eigenvalue formula: eigenvalues of `Hb n b` = range of b
- [ ] Eigenvalue formula: eigenvalues of `Hc n c` = range of c
- [ ] Minimum eigenvalue of `Hb` and `Hc` expressed via `Finset.min'`
- [ ] Continuity of `t ↦ Hint n b c t` (as a map into matrices)

### Phase 3: Main Theorem
- [ ] State the gap condition in terms of b and c
- [ ] Prove the trivial existence theorem (λ_min(H(t)) is the curve)
- [ ] N&S conditions for the spectral gap condition

## Key Lean Conventions

- Index type: `BoolVec n = Fin n → Bool` (has `Fintype`, `DecidableEq`)
- Matrices: `Matrix (BoolVec n) (BoolVec n) ℝ`
- WHT entry: `whtEntry n x y = (-1)^{x·y} / √(2^n)` (noncomputable)
- Build: `lake build AdiabaticGrover 2>&1 | tail -40`

## Session Log

### 2026-03-05 (Initial setup)
- User provided mathematical setup: b, c : {0,1}^n → ℝ, H_b, H_c, H(t)
- Created HANDOFF.md with mathematical analysis
- Created `AdiabaticGrover/Basic.lean` with core definitions (W, Hb, Hc, Hint)
- Created `AdiabaticGrover/MainThm.lean` with main theorem (sorried)
- Build status: TBD
- Next: verify build, prove W_mul_W, flesh out eigenvalue theory

### 2026-03-05 (Session 2)
- Proved `Hb_isHermitian`: `nth_rw 1 [← W_isHermitian n]` + `Matrix.isHermitian_conjTranspose_mul_mul`
- Proved `Hint_isHermitian`: `Matrix.IsHermitian.add` + `Matrix.conjTranspose_smul` + `star_trivial`
- Proved `W_mul_W` (P1): via three helpers:
  - `bitDot_pow_neg1_prod`: factors `(-1)^bitDot` as product over coordinates
  - `bool_wht_factor`: per-bit Bool sum = 2 (if same) or 0 (if different)
  - `wht_orthogonality`: `∑_z (-1)^{x·z} * (-1)^{z·y} = if x=y then 2^n else 0`
    Uses `Finset.prod_mul_distrib` + `(Fintype.prod_sum f).symm` for the sum-product exchange
- Build: clean (only pre-existing sorries remain)
- Remaining sorries: `Hc_eigenvalues`, `Hb_eigenvalues`, `analytic_eigcurve_iff`, `gap_implies_analytic_curve`
- Next: `Hc_eigenvalues` (standard basis eigenvectors of diagonal), then `Hb_eigenvalues` (uses `W_mul_W`)
