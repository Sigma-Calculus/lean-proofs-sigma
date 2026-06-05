/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Mathlib

/-!
# Appendix VI block Laplacian formalization

This file contains the Mathlib formalization of the Appendix VI block
Laplacian construction, including the finite support model, spectral
gap statements, and periodic tensor spectrum certificates.
-/

open scoped BigOperators
open Matrix

namespace Hardtest

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Weighted row-sum vector `d_i = Σ_j S i j`. -/
def blockDegree (S : Matrix n n ℝ) : n → ℝ := fun i => ∑ j, S i j

/-- Diagonal degree matrix `D`. -/
def degreeMatrix (S : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (blockDegree S)

/-- Weighted combinatorial Laplacian `L = D - S`. -/
def weightedLaplacian (S : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (blockDegree S) - S

lemma weightedLaplacian_apply (S : Matrix n n ℝ) (i j : n) :
    weightedLaplacian S i j = (if i = j then blockDegree S i else 0) - S i j := by
  by_cases hij : i = j
  · subst hij
    simp [weightedLaplacian]
  · simp [weightedLaplacian, hij]

lemma weightedLaplacian_quadratic_form
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (x : n → ℝ) :
    2 * (x ⬝ᵥ (weightedLaplacian S).mulVec x) =
      ∑ i, ∑ j, S i j * (x i - x j)^ 2 := by
  classical
  let xx : ℝ := ∑ i, ∑ j, S i j * (x i)^ 2
  let xy : ℝ := ∑ i, ∑ j, S i j * x i * x j
  let yy : ℝ := ∑ i, ∑ j, S i j * (x j)^ 2
  have hsymm_ij : ∀ i j, S i j = S j i := by
    intro i j
    simpa [Matrix.IsSymm, Matrix.transpose_apply] using (congrArg (fun M => M i j) hsymm).symm
  have hyy : yy = xx := by
    dsimp [yy, xx]
    calc
      ∑ i, ∑ j, S i j * (x j)^ 2
          = ∑ j, ∑ i, S i j * (x j)^ 2 := by rw [Finset.sum_comm]
      _ = ∑ j, ∑ i, S j i * (x j)^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro j _
            refine Finset.sum_congr rfl ?_
            intro i _
            rw [hsymm_ij i j]
      _ = ∑ i, ∑ j, S i j * (x i)^ 2 := by rw [Finset.sum_comm]
  have hdiag : x ⬝ᵥ (Matrix.diagonal (blockDegree S)).mulVec x = xx := by
    calc
      x ⬝ᵥ (Matrix.diagonal (blockDegree S)).mulVec x
          = ∑ i, x i * ((Matrix.diagonal (blockDegree S)).mulVec x i) := by rfl
      _ = ∑ i, x i * (blockDegree S i * x i) := by
            simp [Matrix.mulVec_diagonal]
      _ = ∑ i, blockDegree S i * (x i)^ 2 := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring_nf
      _ = xx := by
            dsimp [xx]
            simp [blockDegree, Finset.sum_mul]
  have hS : x ⬝ᵥ S.mulVec x = xy := by
    dsimp [xy]
    simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_left_comm, mul_comm]
  have hdot : x ⬝ᵥ (weightedLaplacian S).mulVec x = xx - xy := by
    calc
      x ⬝ᵥ (weightedLaplacian S).mulVec x
          = x ⬝ᵥ ((Matrix.diagonal (blockDegree S) - S).mulVec x) := by
              simp [weightedLaplacian]
      _ = x ⬝ᵥ ((Matrix.diagonal (blockDegree S)).mulVec x - S.mulVec x) := by
            rw [Matrix.sub_mulVec]
      _ = ∑ i, x i * (((Matrix.diagonal (blockDegree S)).mulVec x) i - (S.mulVec x) i) := by rfl
      _ = ∑ i, (x i * ((Matrix.diagonal (blockDegree S)).mulVec x) i - x i * (S.mulVec x) i) := by
            refine Finset.sum_congr rfl ?_
            intro i _
            ring
      _ =
          ∑ i, x i * ((Matrix.diagonal (blockDegree S)).mulVec x) i -
            ∑ i, x i * (S.mulVec x) i := by
            rw [Finset.sum_sub_distrib]
      _ = x ⬝ᵥ (Matrix.diagonal (blockDegree S)).mulVec x - x ⬝ᵥ S.mulVec x := by rfl
      _ = xx - xy := by rw [hdiag, hS]
  have hexpand : ∑ i, ∑ j, S i j * (x i - x j)^ 2 = xx - 2 * xy + yy := by
    calc
      ∑ i, ∑ j, S i j * (x i - x j)^ 2
          = ∑ i, ∑ j, (S i j * (x i)^ 2 - 2 * (S i j * x i * x j) + S i j * (x j)^ 2) := by
              refine Finset.sum_congr rfl ?_
              intro i _
              refine Finset.sum_congr rfl ?_
              intro j _
              ring
      _ = xx - 2 * xy + yy := by
            dsimp [xx, xy, yy]
            simp_rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
            have hb :
                ∑ i, ∑ j, 2 * (S i j * x i * x j) =
                  2 * (∑ i, ∑ j, S i j * x i * x j) := by
              simp [Finset.mul_sum, two_mul]
            rw [hb]
  calc
    2 * (x ⬝ᵥ (weightedLaplacian S).mulVec x)
        = 2 * (xx - xy) := by rw [hdot]
    _ = xx - xy + (xx - xy) := by ring
    _ = xx - 2 * xy + yy := by rw [hyy]; ring
    _ = ∑ i, ∑ j, S i j * (x i - x j)^ 2 := by rw [hexpand]

end Hardtest

namespace Hardtest

/--
Coordinate form of diagonal action with respect to a finite basis.
This is the reusable algebraic bridge used by Fourier diagonalisation:
once every basis vector is an eigenvector, every vector is acted on
coefficientwise.
-/
lemma eigenbasis_apply_coord
    {β V : Type*} [Finite β] [AddCommGroup V] [Module ℂ V]
    (B : Module.Basis β ℂ V) (T : V →ₗ[ℂ] V) (lam : β → ℂ)
    (hB : ∀ b, T (B b) = lam b • B b)
    (v : V) (b : β) :
    B.equivFun (T v) b = lam b * B.equivFun v b := by
  classical
  letI := Fintype.ofFinite β
  calc
    B.equivFun (T v) b =
        B.equivFun (T (∑ c, B.equivFun v c • B c)) b := by
      rw [B.sum_equivFun v]
    _ = B.equivFun (∑ c, B.equivFun v c • T (B c)) b := by
      rw [map_sum]
      simp [map_smul]
    _ = B.equivFun (∑ c, B.equivFun v c • (lam c • B c)) b := by
      simp [hB]
    _ = B.equivFun (∑ c, (B.equivFun v c * lam c) • B c) b := by
      simp [smul_smul, mul_assoc]
    _ = B.equivFun v b * lam b := by
      have hsum :
          (∑ x, (B.repr v) x * lam x * (Finsupp.single x (1 : ℂ)) b) =
            (B.repr v) b * lam b * (Finsupp.single b (1 : ℂ)) b := by
        refine Finset.sum_eq_single (s := Finset.univ)
          (f := fun x => (B.repr v) x * lam x * (Finsupp.single x (1 : ℂ)) b) b ?_ ?_
        · intro x _ hxb
          simp [Finsupp.single_eq_of_ne hxb.symm]
        · intro hb
          simp at hb
      simpa [Module.Basis.equivFun_apply] using hsum
    _ = lam b * B.equivFun v b := by ring

/--
If a finite basis diagonalises a complex linear operator, then any eigenvalue
of that operator is one of the diagonal basis eigenvalues.
-/
lemma eigenvalue_mem_range_of_eigenbasis
    {β V : Type*} [Finite β] [AddCommGroup V] [Module ℂ V]
    (B : Module.Basis β ℂ V) (T : V →ₗ[ℂ] V) (lam : β → ℂ)
    (hB : ∀ b, T (B b) = lam b • B b)
    {μ : ℂ} {v : V} (hv : T v = μ • v) (hvne : v ≠ 0) :
    ∃ b, lam b = μ := by
  classical
  letI := Fintype.ofFinite β
  have hcoeff_nonzero : ∃ b, B.equivFun v b ≠ 0 := by
    by_contra h
    push Not at h
    apply hvne
    have hvzero : B.equivFun v = B.equivFun 0 := by
      ext b
      simp [h b]
    exact B.equivFun.injective hvzero
  rcases hcoeff_nonzero with ⟨b, hb⟩
  have hcoordT := eigenbasis_apply_coord B T lam hB v b
  have hcoordμ : B.equivFun (T v) b = μ * B.equivFun v b := by
    rw [hv]
    simp
  have heq : lam b * B.equivFun v b = μ * B.equivFun v b := by
    rw [← hcoordT, hcoordμ]
  exact ⟨b, mul_right_cancel₀ hb heq⟩

/--
Complexification of the row-action of a real finite matrix.  This lets the
real Appendix-VI block Laplacian be diagonalised with Mathlib's complex
finite-abelian character basis.
-/
noncomputable def realMatrixComplexMulVecLinearMap
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) : (ι → ℂ) →ₗ[ℂ] (ι → ℂ) :=
  Matrix.toLin' (A.map (algebraMap ℝ ℂ))

lemma realMatrixComplexMulVecLinearMap_apply
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℂ) (i : ι) :
    realMatrixComplexMulVecLinearMap A v i = ∑ j, (A i j : ℂ) * v j := by
  simp [realMatrixComplexMulVecLinearMap, Matrix.toLin'_apply, Matrix.mulVec,
    Matrix.map_apply, dotProduct]

lemma realMatrixComplexMulVecLinearMap_ofReal
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) (v : ι → ℝ) :
    realMatrixComplexMulVecLinearMap A (fun i => (v i : ℂ)) =
      fun i => ((A.mulVec v i : ℝ) : ℂ) := by
  ext i
  simp [realMatrixComplexMulVecLinearMap_apply, Matrix.mulVec, dotProduct]

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
lemma entry_symm {S : Matrix n n ℝ} (hsymm : S.IsSymm) (i j : n) : S i j = S j i := by
  simpa [Matrix.IsSymm, Matrix.transpose_apply] using (congrArg (fun M => M i j) hsymm).symm

omit [Fintype n] [DecidableEq n] in
lemma realMatrix_isHermitian_of_isSymm {ι : Type*} {A : Matrix ι ι ℝ} (hA : A.IsSymm) :
    A.IsHermitian := by
  rw [Matrix.IsHermitian]
  ext i j
  simp [Matrix.conjTranspose_apply]
  simpa [Matrix.IsSymm, Matrix.transpose_apply] using
    congrArg (fun M : Matrix ι ι ℝ => M i j) hA

omit [DecidableEq n] in
lemma vecMul_eq_mulVec_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm) (x : n → ℝ) :
    x ᵥ* A = A.mulVec x := by
  calc
    x ᵥ* A = x ᵥ* Aᵀ := by rw [hA]
    _ = A.mulVec x := by rw [Matrix.vecMul_transpose]

omit [DecidableEq n] in
lemma dotProduct_mulVec_comm_of_isSymm {A : Matrix n n ℝ} (hA : A.IsSymm)
    (x y : n → ℝ) :
    x ⬝ᵥ A.mulVec y = y ⬝ᵥ A.mulVec x := by
  rw [Matrix.dotProduct_mulVec]
  rw [vecMul_eq_mulVec_of_isSymm hA x]
  exact dotProduct_comm (A.mulVec x) y

lemma weightedLaplacian_isSymm
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) :
    (weightedLaplacian S).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.transpose_apply]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Matrix.transpose_apply, weightedLaplacian_apply, hij, hji,
      entry_symm hsymm j i]

lemma weightedLaplacian_dotProduct_comm
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (x y : n → ℝ) :
    x ⬝ᵥ (weightedLaplacian S).mulVec y =
      y ⬝ᵥ (weightedLaplacian S).mulVec x := by
  exact dotProduct_mulVec_comm_of_isSymm
    (weightedLaplacian_isSymm S hsymm) x y

lemma weightedLaplacian_posSemidef
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j) :
    (weightedLaplacian S).PosSemidef := by
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · change (weightedLaplacian S)ᴴ = weightedLaplacian S
    ext i j
    by_cases hij : i = j
    · subst hij
      simp [weightedLaplacian_apply]
    · have hji : j ≠ i := fun h => hij h.symm
      simp [Matrix.conjTranspose_apply, weightedLaplacian_apply, hij, hji, entry_symm hsymm j i]
  · intro x
    have hq := weightedLaplacian_quadratic_form S hsymm x
    have hsumnn : 0 ≤ ∑ i, ∑ j, S i j * (x i - x j)^ 2 := by
      refine Finset.sum_nonneg ?_
      intro i _
      refine Finset.sum_nonneg ?_
      intro j _
      exact mul_nonneg (hnonneg i j) (sq_nonneg _)
    have hdot : 0 ≤ x ⬝ᵥ (weightedLaplacian S).mulVec x := by
      nlinarith
    simpa using hdot


end Hardtest

namespace Hardtest

variable {n : Type*} [Fintype n] [DecidableEq n]

def supportGraph (S : Matrix n n ℝ) (hsymm : S.IsSymm) : SimpleGraph n where
  Adj i j := i ≠ j ∧ 0 < S i j
  symm := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    simpa [entry_symm hsymm i j] using hij.2

lemma weightedLaplacian_mulVec_eq_zero_iff_exists_const
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hconn : (supportGraph S hsymm).Connected) (x : n → ℝ) :
    (weightedLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  constructor
  · intro hx
    have hq := weightedLaplacian_quadratic_form S hsymm x
    have hdot0 : x ⬝ᵥ (weightedLaplacian S).mulVec x = 0 := by
      simp [hx]
    have hsum0 : ∑ i, ∑ j, S i j * (x i - x j)^ 2 = 0 := by
      nlinarith [hq, hdot0]
    have houter_nonneg : ∀ i, 0 ≤ ∑ j, S i j * (x i - x j)^ 2 := by
      intro i
      refine Finset.sum_nonneg ?_
      intro j _
      exact mul_nonneg (hnonneg i j) (sq_nonneg _)
    have houter_zero : ∀ i, ∑ j, S i j * (x i - x j)^ 2 = 0 := by
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => houter_nonneg i)).mp hsum0
      intro i
      exact h i (Finset.mem_univ i)
    have hinner_zero : ∀ i j, S i j * (x i - x j)^ 2 = 0 := by
      intro i j
      have hinner_nonneg : ∀ j, 0 ≤ S i j * (x i - x j)^ 2 := by
        intro j
        exact mul_nonneg (hnonneg i j) (sq_nonneg _)
      have h := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hinner_nonneg j)).mp (houter_zero i)
      exact h j (Finset.mem_univ j)
    have hedge_eq : ∀ i j, (supportGraph S hsymm).Adj i j → x i = x j := by
      intro i j hij
      have hsq : (x i - x j)^ 2 = 0 := by
        have hmul := hinner_zero i j
        exact (mul_eq_zero.mp hmul).resolve_left (ne_of_gt hij.2)
      nlinarith
    have hwalk_eq : ∀ {i j}, (supportGraph S hsymm).Walk i j → x i = x j := by
      intro i j w
      induction w with
      | nil => rfl
      | cons hij w ih => exact (hedge_eq _ _ hij).trans ih
    have hreach_eq : ∀ i j, (supportGraph S hsymm).Reachable i j → x i = x j := by
      intro i j hreach
      exact hreach.elim (fun w => hwalk_eq w)
    letI := hconn.nonempty
    let i0 : n := Classical.choice hconn.nonempty
    refine ⟨x i0, funext fun j => ?_⟩
    exact hreach_eq j i0 (hconn j i0)
  · rintro ⟨c, rfl⟩
    ext i
    rw [weightedLaplacian, Matrix.sub_mulVec]
    change
      (∑ x, Matrix.diagonal (blockDegree S) i x * c) -
          ∑ x, S i x * c = 0
    have hdiag : ∑ x, Matrix.diagonal (blockDegree S) i x * c = blockDegree S i * c := by
      simp [Matrix.diagonal]
    rw [hdiag]
    change (∑ x, S i x) * c - ∑ x, S i x * c = 0
    rw [Finset.sum_mul]
    ring


end Hardtest

namespace Hardtest

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Diagonal inverse degree matrix `D^{-1}`. -/
noncomputable def inverseDegreeMatrix (S : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal (fun i => (blockDegree S i)⁻¹)

lemma degreeMatrix_mul_inverseDegreeMatrix
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0) :
    degreeMatrix S * inverseDegreeMatrix S = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [degreeMatrix, inverseDegreeMatrix, hdeg i]
  · simp [degreeMatrix, inverseDegreeMatrix, hij]

/-- Random-walk matrix `W = D^{-1} S`. -/
noncomputable def randomWalkMatrix (S : Matrix n n ℝ) : Matrix n n ℝ :=
  inverseDegreeMatrix S * S

/-- Entrywise form of the row-normalized random-walk matrix. -/
lemma randomWalkMatrix_apply (S : Matrix n n ℝ) (i j : n) :
    randomWalkMatrix S i j = (blockDegree S i)⁻¹ * S i j := by
  rw [randomWalkMatrix, inverseDegreeMatrix, Matrix.diagonal_mul]

/-- Random-walk Laplacian in the Appendix-VI form `A = I - W`. -/
noncomputable def randomWalkLaplacian (S : Matrix n n ℝ) : Matrix n n ℝ :=
  1 - randomWalkMatrix S

/-- Entrywise form of the random-walk Laplacian. -/
lemma randomWalkLaplacian_apply (S : Matrix n n ℝ) (i j : n) :
    randomWalkLaplacian S i j =
      (if i = j then 1 else 0) - (blockDegree S i)⁻¹ * S i j := by
  simp [randomWalkLaplacian, randomWalkMatrix_apply, Matrix.one_apply]

lemma randomWalkLaplacian_offdiag_eq_zero_of_weight_zero
    (S : Matrix n n ℝ) {i j : n} (hij : i ≠ j) (hS : S i j = 0) :
    randomWalkLaplacian S i j = 0 := by
  simp [randomWalkLaplacian_apply, hij, hS]

/--
The random-walk Laplacian is symmetric in the ordinary Euclidean coordinates
when the underlying symmetric weight matrix has constant row degree.
-/
lemma randomWalkLaplacian_isSymm_of_constant_blockDegree
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) {d : ℝ}
    (hdeg : ∀ i, blockDegree S i = d) :
    (randomWalkLaplacian S).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.transpose_apply]
  · have hji : j ≠ i := fun h => hij h.symm
    simp [Matrix.transpose_apply, randomWalkLaplacian_apply, hij, hji,
      hdeg i, hdeg j, entry_symm hsymm j i]

/-- Degree-weighted bilinear form `<x,y>_D = Σ_i d_i x_i y_i`. -/
def degreeWeightedDot (S : Matrix n n ℝ) (x y : n → ℝ) : ℝ :=
  ∑ i, blockDegree S i * x i * y i

omit [DecidableEq n] in
lemma degreeWeightedDot_comm (S : Matrix n n ℝ) (x y : n → ℝ) :
    degreeWeightedDot S x y = degreeWeightedDot S y x := by
  unfold degreeWeightedDot
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

lemma degreeWeightedDot_eq_dotProduct_degreeMatrix_mulVec
    (S : Matrix n n ℝ) (x y : n → ℝ) :
    degreeWeightedDot S x y = x ⬝ᵥ (degreeMatrix S).mulVec y := by
  unfold degreeWeightedDot degreeMatrix
  simp only [Matrix.mulVec_diagonal, dotProduct]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

omit [DecidableEq n] in
lemma degreeWeightedDot_self_eq_sum (S : Matrix n n ℝ) (x : n → ℝ) :
    degreeWeightedDot S x x = ∑ i, blockDegree S i * (x i)^ 2 := by
  unfold degreeWeightedDot
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

omit [DecidableEq n] in
lemma degreeWeightedDot_self_nonneg
    (S : Matrix n n ℝ) (hdeg_nonneg : ∀ i, 0 ≤ blockDegree S i) (x : n → ℝ) :
    0 ≤ degreeWeightedDot S x x := by
  rw [degreeWeightedDot_self_eq_sum]
  refine Finset.sum_nonneg ?_
  intro i _
  exact mul_nonneg (hdeg_nonneg i) (sq_nonneg _)

omit [DecidableEq n] in
lemma degreeWeightedDot_self_eq_zero_iff
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) (x : n → ℝ) :
    degreeWeightedDot S x x = 0 ↔ x = 0 := by
  constructor
  · intro h
    rw [degreeWeightedDot_self_eq_sum] at h
    have hnonneg : ∀ i, 0 ≤ blockDegree S i * (x i)^ 2 := by
      intro i
      exact mul_nonneg (le_of_lt (hpos i)) (sq_nonneg _)
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => hnonneg i)).mp h
    ext i
    have hi := hzero i (Finset.mem_univ i)
    have hsq : (x i)^ 2 = 0 := by
      exact (mul_eq_zero.mp hi).resolve_left (ne_of_gt (hpos i))
    exact sq_eq_zero_iff.mp hsq
  · intro hx
    simp [hx, degreeWeightedDot_self_eq_sum]

omit [DecidableEq n] in
lemma degreeWeightedDot_self_pos_of_ne_zero
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i)
    {x : n → ℝ} (hx : x ≠ 0) :
    0 < degreeWeightedDot S x x := by
  have hnonneg : 0 ≤ degreeWeightedDot S x x :=
    degreeWeightedDot_self_nonneg S (fun i => le_of_lt (hpos i)) x
  have hne : degreeWeightedDot S x x ≠ 0 := by
    intro hzero
    exact hx ((degreeWeightedDot_self_eq_zero_iff S hpos x).mp hzero)
  exact lt_of_le_of_ne hnonneg (Ne.symm hne)

/-- Weighted cut size across a subset of vertices. -/
def weightedCut (S : Matrix n n ℝ) (U : Finset n) : ℝ :=
  U.sum fun i => ((Finset.univ : Finset n) \ U).sum fun j => S i j

/-- Weighted volume of a subset for the overlap graph. -/
def weightedVolume (S : Matrix n n ℝ) (U : Finset n) : ℝ :=
  U.sum fun i => blockDegree S i

/--
Cheeger lower-bound statement without division by the volume.
This is the form used by Appendix VI's uniform conductance hypothesis.
-/
def WeightedCheegerLowerBound (S : Matrix n n ℝ) (h0 : ℝ) : Prop :=
  ∀ U : Finset n,
    U.Nonempty → 2 * U.card ≤ Fintype.card n →
      h0 * weightedVolume S U ≤ weightedCut S U

/-- The same operator written as `D^{-1} L`. -/
noncomputable def scaledWeightedLaplacian (S : Matrix n n ℝ) : Matrix n n ℝ :=
  inverseDegreeMatrix S * weightedLaplacian S

lemma scaledWeightedLaplacian_mulVec_apply
    (S : Matrix n n ℝ) (x : n → ℝ) (i : n) :
    (scaledWeightedLaplacian S).mulVec x i =
      (blockDegree S i)⁻¹ * (weightedLaplacian S).mulVec x i := by
  rw [scaledWeightedLaplacian, ← Matrix.mulVec_mulVec, inverseDegreeMatrix,
    Matrix.mulVec_diagonal]

lemma scaledWeightedLaplacian_mulVec_eq_zero_iff_weightedLaplacian
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0) (x : n → ℝ) :
    (scaledWeightedLaplacian S).mulVec x = 0 ↔ (weightedLaplacian S).mulVec x = 0 := by
  constructor
  · intro h
    ext i
    have hi := congrFun h i
    rw [scaledWeightedLaplacian_mulVec_apply S x i] at hi
    exact (mul_eq_zero.mp hi).resolve_left (inv_ne_zero (hdeg i))
  · intro h
    ext i
    rw [scaledWeightedLaplacian_mulVec_apply S x i, h]
    simp

lemma randomWalkLaplacian_eq_scaledWeightedLaplacian
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0) :
    randomWalkLaplacian S = scaledWeightedLaplacian S := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [randomWalkLaplacian, randomWalkMatrix, scaledWeightedLaplacian,
      inverseDegreeMatrix, weightedLaplacian, blockDegree]
    have hd : (∑ j, S i j) ≠ 0 := by
      simpa [blockDegree] using hdeg i
    field_simp [hd]
  · simp [randomWalkLaplacian, randomWalkMatrix, scaledWeightedLaplacian,
      inverseDegreeMatrix, weightedLaplacian, blockDegree, hij]

lemma degreeMatrix_mul_randomWalkLaplacian
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0) :
    degreeMatrix S * randomWalkLaplacian S = weightedLaplacian S := by
  calc
    degreeMatrix S * randomWalkLaplacian S =
        degreeMatrix S * scaledWeightedLaplacian S := by
      rw [randomWalkLaplacian_eq_scaledWeightedLaplacian S hdeg]
    _ = degreeMatrix S * (inverseDegreeMatrix S * weightedLaplacian S) := by
      rw [scaledWeightedLaplacian]
    _ = (degreeMatrix S * inverseDegreeMatrix S) * weightedLaplacian S := by
      rw [Matrix.mul_assoc]
    _ = weightedLaplacian S := by
      rw [degreeMatrix_mul_inverseDegreeMatrix S hdeg]
      simp

lemma degreeWeightedDot_randomWalkLaplacian_right_eq_dotProduct_weightedLaplacian
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0)
    (x y : n → ℝ) :
    degreeWeightedDot S x ((randomWalkLaplacian S).mulVec y) =
      x ⬝ᵥ (weightedLaplacian S).mulVec y := by
  rw [degreeWeightedDot_eq_dotProduct_degreeMatrix_mulVec]
  have hvec :
      (degreeMatrix S).mulVec ((randomWalkLaplacian S).mulVec y) =
        (weightedLaplacian S).mulVec y := by
    rw [Matrix.mulVec_mulVec]
    rw [degreeMatrix_mul_randomWalkLaplacian S hdeg]
  rw [hvec]

theorem randomWalkLaplacian_degreeWeighted_selfAdjoint
    (S : Matrix n n ℝ) (hsymm : S.IsSymm)
    (hdeg : ∀ i, blockDegree S i ≠ 0) (x y : n → ℝ) :
    degreeWeightedDot S x ((randomWalkLaplacian S).mulVec y) =
      degreeWeightedDot S ((randomWalkLaplacian S).mulVec x) y := by
  calc
    degreeWeightedDot S x ((randomWalkLaplacian S).mulVec y) =
        x ⬝ᵥ (weightedLaplacian S).mulVec y := by
      exact degreeWeightedDot_randomWalkLaplacian_right_eq_dotProduct_weightedLaplacian
        S hdeg x y
    _ = y ⬝ᵥ (weightedLaplacian S).mulVec x := by
      exact weightedLaplacian_dotProduct_comm S hsymm x y
    _ = degreeWeightedDot S y ((randomWalkLaplacian S).mulVec x) := by
      symm
      exact degreeWeightedDot_randomWalkLaplacian_right_eq_dotProduct_weightedLaplacian
        S hdeg y x
    _ = degreeWeightedDot S ((randomWalkLaplacian S).mulVec x) y := by
      exact degreeWeightedDot_comm S y ((randomWalkLaplacian S).mulVec x)

theorem randomWalkLaplacian_degreeWeighted_quadratic_form
    (S : Matrix n n ℝ) (hsymm : S.IsSymm)
    (hdeg : ∀ i, blockDegree S i ≠ 0) (x : n → ℝ) :
    2 * degreeWeightedDot S x ((randomWalkLaplacian S).mulVec x) =
      ∑ i, ∑ j, S i j * (x i - x j)^ 2 := by
  rw [degreeWeightedDot_randomWalkLaplacian_right_eq_dotProduct_weightedLaplacian
    S hdeg]
  exact weightedLaplacian_quadratic_form S hsymm x

theorem randomWalkLaplacian_degreeWeighted_dirichlet_nonneg
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hdeg : ∀ i, blockDegree S i ≠ 0) (x : n → ℝ) :
    0 ≤ degreeWeightedDot S x ((randomWalkLaplacian S).mulVec x) := by
  have hq := randomWalkLaplacian_degreeWeighted_quadratic_form S hsymm hdeg x
  have hsumnn : 0 ≤ ∑ i, ∑ j, S i j * (x i - x j)^ 2 := by
    refine Finset.sum_nonneg ?_
    intro i _
    refine Finset.sum_nonneg ?_
    intro j _
    exact mul_nonneg (hnonneg i j) (sq_nonneg _)
  nlinarith

lemma randomWalkLaplacian_mulVec_eq_zero_iff_weightedLaplacian
    (S : Matrix n n ℝ) (hdeg : ∀ i, blockDegree S i ≠ 0) (x : n → ℝ) :
    (randomWalkLaplacian S).mulVec x = 0 ↔ (weightedLaplacian S).mulVec x = 0 := by
  rw [randomWalkLaplacian_eq_scaledWeightedLaplacian S hdeg]
  exact scaledWeightedLaplacian_mulVec_eq_zero_iff_weightedLaplacian S hdeg x

lemma randomWalkLaplacian_mulVec_eq_zero_iff_exists_const
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hdeg : ∀ i, blockDegree S i ≠ 0)
    (hconn : (supportGraph S hsymm).Connected) (x : n → ℝ) :
    (randomWalkLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  rw [randomWalkLaplacian_mulVec_eq_zero_iff_weightedLaplacian S hdeg x]
  exact weightedLaplacian_mulVec_eq_zero_iff_exists_const S hsymm hnonneg hconn x

/-- Diagonal square-root degree matrix `D^{1/2}`. -/
noncomputable def degreeSqrtMatrix (S : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal fun i => √(blockDegree S i)

/-- Diagonal inverse square-root degree matrix `D^{-1/2}`. -/
noncomputable def inverseDegreeSqrtMatrix (S : Matrix n n ℝ) : Matrix n n ℝ :=
  Matrix.diagonal fun i => (√(blockDegree S i))⁻¹

/-- Symmetric normalized Laplacian `D^{-1/2} L D^{-1/2}`. -/
noncomputable def similaritySymmetrizedLaplacian (S : Matrix n n ℝ) : Matrix n n ℝ :=
  (inverseDegreeSqrtMatrix S)ᴴ * weightedLaplacian S * inverseDegreeSqrtMatrix S

lemma similaritySymmetrizedLaplacian_posSemidef
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j) :
    (similaritySymmetrizedLaplacian S).PosSemidef := by
  simpa [similaritySymmetrizedLaplacian] using
    (weightedLaplacian_posSemidef S hsymm hnonneg).conjTranspose_mul_mul_same
      (inverseDegreeSqrtMatrix S)

/--
Cheeger certificate for the symmetric normalised block Laplacian.
The `spectral_gap_bound` field is the theorem-level Cheeger step
`λ₂ ≥ h₀² / 2` for the non-zero spectrum.
-/
structure WeightedCheegerGapCertificate (S : Matrix n n ℝ) where
  h0 : ℝ
  h0_pos : 0 < h0
  lower_bound : WeightedCheegerLowerBound S h0
  spectral_gap_bound :
    ∀ μ ∈ spectrum ℝ (similaritySymmetrizedLaplacian S),
      μ ≠ 0 → h0 ^ 2 / 2 ≤ μ

lemma cheegerGapValue_pos (S : Matrix n n ℝ)
    (C : WeightedCheegerGapCertificate S) :
    0 < C.h0 ^ 2 / 2 := by
  have hsquare : 0 < C.h0 ^ 2 := sq_pos_of_ne_zero (ne_of_gt C.h0_pos)
  nlinarith

lemma inverseDegreeSqrtMatrix_conjTranspose (S : Matrix n n ℝ) :
    (inverseDegreeSqrtMatrix S)ᴴ = inverseDegreeSqrtMatrix S := by
  simp [inverseDegreeSqrtMatrix]

lemma degreeSqrtMatrix_mul_inverseDegreeMatrix
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    degreeSqrtMatrix S * inverseDegreeMatrix S = inverseDegreeSqrtMatrix S := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [degreeSqrtMatrix, inverseDegreeMatrix, inverseDegreeSqrtMatrix]
    have hroot : √(blockDegree S i) ≠ 0 := (Real.sqrt_ne_zero').2 (hpos i)
    have hdeg : blockDegree S i ≠ 0 := ne_of_gt (hpos i)
    field_simp [hroot, hdeg]
    rw [Real.sq_sqrt (le_of_lt (hpos i))]
  · simp [degreeSqrtMatrix, inverseDegreeMatrix, inverseDegreeSqrtMatrix, hij]

lemma degreeSqrtMatrix_mul_inverseDegreeSqrtMatrix
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    degreeSqrtMatrix S * inverseDegreeSqrtMatrix S = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [degreeSqrtMatrix, inverseDegreeSqrtMatrix,
      (Real.sqrt_ne_zero').2 (hpos i)]
  · simp [degreeSqrtMatrix, inverseDegreeSqrtMatrix, hij]

lemma inverseDegreeSqrtMatrix_mul_degreeSqrtMatrix
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    inverseDegreeSqrtMatrix S * degreeSqrtMatrix S = 1 := by
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [degreeSqrtMatrix, inverseDegreeSqrtMatrix,
      (Real.sqrt_ne_zero').2 (hpos i)]
  · simp [degreeSqrtMatrix, inverseDegreeSqrtMatrix, hij]

lemma similaritySymmetrizedLaplacian_eq_sqrt_conj_randomWalkLaplacian
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    similaritySymmetrizedLaplacian S =
      degreeSqrtMatrix S * randomWalkLaplacian S * inverseDegreeSqrtMatrix S := by
  have hdeg : ∀ i, blockDegree S i ≠ 0 := fun i => ne_of_gt (hpos i)
  calc
    similaritySymmetrizedLaplacian S =
        inverseDegreeSqrtMatrix S * weightedLaplacian S * inverseDegreeSqrtMatrix S := by
      rw [similaritySymmetrizedLaplacian, inverseDegreeSqrtMatrix_conjTranspose]
    _ = degreeSqrtMatrix S * randomWalkLaplacian S * inverseDegreeSqrtMatrix S := by
      rw [randomWalkLaplacian_eq_scaledWeightedLaplacian S hdeg, scaledWeightedLaplacian]
      rw [← Matrix.mul_assoc (degreeSqrtMatrix S) (inverseDegreeMatrix S)
        (weightedLaplacian S)]
      rw [degreeSqrtMatrix_mul_inverseDegreeMatrix S hpos]

lemma degreeSqrtMatrix_isUnit
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    IsUnit (degreeSqrtMatrix S) := by
  rw [degreeSqrtMatrix, Matrix.isUnit_diagonal, Pi.isUnit_iff]
  intro i
  exact isUnit_iff_ne_zero.mpr ((Real.sqrt_ne_zero').2 (hpos i))

noncomputable def degreeSqrtUnit
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    (Matrix n n ℝ)ˣ :=
  (degreeSqrtMatrix_isUnit S hpos).unit

lemma degreeSqrtUnit_val
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    ((degreeSqrtUnit S hpos : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) =
      degreeSqrtMatrix S :=
  (degreeSqrtMatrix_isUnit S hpos).unit_spec

lemma degreeSqrtUnit_inv_val
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    (((degreeSqrtUnit S hpos)⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) =
      inverseDegreeSqrtMatrix S := by
  let u := degreeSqrtUnit S hpos
  have hu : (u : Matrix n n ℝ) = degreeSqrtMatrix S :=
    degreeSqrtUnit_val S hpos
  have hmul : (u : Matrix n n ℝ) * inverseDegreeSqrtMatrix S = 1 := by
    rw [hu]
    exact degreeSqrtMatrix_mul_inverseDegreeSqrtMatrix S hpos
  calc
    ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)
        = ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) * 1 := by
      rw [mul_one]
    _ = ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
          ((u : Matrix n n ℝ) * inverseDegreeSqrtMatrix S) := by
      rw [hmul]
    _ = (((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
          (u : Matrix n n ℝ)) * inverseDegreeSqrtMatrix S := by
      rw [Matrix.mul_assoc]
    _ = inverseDegreeSqrtMatrix S := by
      simp

lemma randomWalkLaplacian_spectrum_eq_similaritySymmetrizedLaplacian
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i) :
    spectrum ℝ (randomWalkLaplacian S) =
      spectrum ℝ (similaritySymmetrizedLaplacian S) := by
  let u := degreeSqrtUnit S hpos
  have hu : (u : Matrix n n ℝ) = degreeSqrtMatrix S :=
    degreeSqrtUnit_val S hpos
  have huinv :
      ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) =
        inverseDegreeSqrtMatrix S := by
    exact degreeSqrtUnit_inv_val S hpos
  have hconj :
      similaritySymmetrizedLaplacian S =
        (u : Matrix n n ℝ) * randomWalkLaplacian S *
          ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    calc
      similaritySymmetrizedLaplacian S =
          degreeSqrtMatrix S * randomWalkLaplacian S *
            inverseDegreeSqrtMatrix S := by
        exact similaritySymmetrizedLaplacian_eq_sqrt_conj_randomWalkLaplacian S hpos
      _ = (u : Matrix n n ℝ) * randomWalkLaplacian S *
            ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
        rw [hu, huinv]
  rw [hconj]
  symm
  simpa using
    (spectrum.units_conjugate (R := ℝ) (a := randomWalkLaplacian S) (u := u))

lemma randomWalkLaplacian_spectrum_nonneg
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i) :
    ∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), 0 ≤ μ := by
  let u := degreeSqrtUnit S hpos
  have hu : (u : Matrix n n ℝ) = degreeSqrtMatrix S :=
    degreeSqrtUnit_val S hpos
  have huinv :
      ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) =
        inverseDegreeSqrtMatrix S := by
    exact degreeSqrtUnit_inv_val S hpos
  have hconj :
      similaritySymmetrizedLaplacian S =
        (u : Matrix n n ℝ) * randomWalkLaplacian S *
          ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    calc
      similaritySymmetrizedLaplacian S =
          degreeSqrtMatrix S * randomWalkLaplacian S *
            inverseDegreeSqrtMatrix S := by
        exact similaritySymmetrizedLaplacian_eq_sqrt_conj_randomWalkLaplacian S hpos
      _ = (u : Matrix n n ℝ) * randomWalkLaplacian S *
            ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
        rw [hu, huinv]
  have hspectrum :
      spectrum ℝ (randomWalkLaplacian S) =
        spectrum ℝ (similaritySymmetrizedLaplacian S) := by
    rw [hconj]
    symm
    simpa using
      (spectrum.units_conjugate (R := ℝ) (a := randomWalkLaplacian S) (u := u))
  have hpsd := similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg
  intro μ hμ
  have hμhat : μ ∈ spectrum ℝ (similaritySymmetrizedLaplacian S) := by
    simpa [hspectrum] using hμ
  rw [hpsd.isHermitian.spectrum_real_eq_range_eigenvalues] at hμhat
  rcases hμhat with ⟨i, rfl⟩
  exact hpsd.eigenvalues_nonneg i

lemma finite_nonzero_spectral_gap
    {s : Set ℝ} (hs : s.Finite) (hnonneg : ∀ μ ∈ s, 0 ≤ μ) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ μ ∈ s, μ ≠ 0 → γ ≤ μ := by
  classical
  let positivePart : Set ℝ := { μ | μ ∈ s ∧ μ ≠ 0 }
  by_cases hpositivePart : positivePart.Nonempty
  · have hpositivePartFinite : positivePart.Finite :=
      hs.subset (by
        intro μ hμ
        exact hμ.1)
    obtain ⟨μ0, hμ0, hmin⟩ :=
      Set.exists_min_image positivePart (fun μ : ℝ => μ)
        hpositivePartFinite hpositivePart
    have hμ0pos : 0 < μ0 :=
      lt_of_le_of_ne (hnonneg μ0 hμ0.1) (Ne.symm hμ0.2)
    refine ⟨μ0, hμ0pos, ?_⟩
    intro μ hμ hμne
    exact hmin μ ⟨hμ, hμne⟩
  · refine ⟨1, by norm_num, ?_⟩
    intro μ hμ hμne
    exact (hpositivePart ⟨μ, hμ, hμne⟩).elim

lemma finite_first_positive_spectral_value
    {s : Set ℝ} (hs : s.Finite) (hnonneg : ∀ μ ∈ s, 0 ≤ μ)
    (hnonzero : ∃ μ : ℝ, μ ∈ s ∧ μ ≠ 0) :
    ∃ lam : ℝ, 0 < lam ∧ lam ∈ s ∧
      ∀ μ ∈ s, μ ≠ 0 → lam ≤ μ := by
  classical
  let positivePart : Set ℝ := { μ | μ ∈ s ∧ μ ≠ 0 }
  have hpositivePart : positivePart.Nonempty := by
    rcases hnonzero with ⟨μ, hμ, hμne⟩
    exact ⟨μ, hμ, hμne⟩
  have hpositivePartFinite : positivePart.Finite :=
    hs.subset (by
      intro μ hμ
      exact hμ.1)
  obtain ⟨lam, hlam, hmin⟩ :=
    Set.exists_min_image positivePart (fun μ : ℝ => μ)
      hpositivePartFinite hpositivePart
  have hlampos : 0 < lam :=
    lt_of_le_of_ne (hnonneg lam hlam.1) (Ne.symm hlam.2)
  refine ⟨lam, hlampos, hlam.1, ?_⟩
  intro μ hμ hμne
  exact hmin μ ⟨hμ, hμne⟩

lemma randomWalkLaplacian_positive_spectral_gap
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), μ ≠ 0 → γ ≤ μ := by
  exact finite_nonzero_spectral_gap
    ((randomWalkLaplacian S).finite_real_spectrum)
    (randomWalkLaplacian_spectrum_nonneg S hsymm hnonneg hpos)

omit [DecidableEq n] in
lemma matrix_ne_zero_of_constant_kernel
    (A : Matrix n n ℝ) [Nontrivial n]
    (hker : ∀ x : n → ℝ, A.mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c) :
    A ≠ 0 := by
  classical
  obtain ⟨a, b, hab⟩ := exists_pair_ne n
  let x : n → ℝ := fun i => if i = a then 1 else 0
  have hx_nonconst : ¬ ∃ c : ℝ, x = fun _ => c := by
    rintro ⟨c, hc⟩
    have ha : x a = c := by simpa using congrFun hc a
    have hb : x b = c := by simpa using congrFun hc b
    have hxa : x a = 1 := by simp [x]
    have hxb : x b = 0 := by simp [x, hab.symm]
    nlinarith
  intro hA0
  have hxker : A.mulVec x = 0 := by simp [hA0]
  exact hx_nonconst ((hker x).mp hxker)

lemma isHermitian_exists_nonzero_real_spectrum
    {A : Matrix n n ℝ} (hA : A.IsHermitian) (h_ne : A ≠ 0) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ A ∧ μ ≠ 0 := by
  classical
  have heig_ne : hA.eigenvalues ≠ 0 := by
    intro heig
    exact h_ne ((hA.eigenvalues_eq_zero_iff).mp heig)
  obtain ⟨i, hi⟩ := Function.ne_iff.mp heig_ne
  exact ⟨hA.eigenvalues i, hA.eigenvalues_mem_spectrum_real i, by simpa using hi⟩

lemma similaritySymmetrizedLaplacian_ne_zero_of_randomWalkLaplacian_ne_zero
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i)
    (hrw_ne : randomWalkLaplacian S ≠ 0) :
    similaritySymmetrizedLaplacian S ≠ 0 := by
  classical
  intro hsym_zero
  let u := degreeSqrtUnit S hpos
  have hu : (u : Matrix n n ℝ) = degreeSqrtMatrix S :=
    degreeSqrtUnit_val S hpos
  have huinv :
      ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) =
        inverseDegreeSqrtMatrix S := by
    exact degreeSqrtUnit_inv_val S hpos
  have hconj :
      similaritySymmetrizedLaplacian S =
        (u : Matrix n n ℝ) * randomWalkLaplacian S *
          ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
    calc
      similaritySymmetrizedLaplacian S =
          degreeSqrtMatrix S * randomWalkLaplacian S *
            inverseDegreeSqrtMatrix S := by
        exact similaritySymmetrizedLaplacian_eq_sqrt_conj_randomWalkLaplacian S hpos
      _ = (u : Matrix n n ℝ) * randomWalkLaplacian S *
            ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) := by
        rw [hu, huinv]
  have hback :
      ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
          similaritySymmetrizedLaplacian S * (u : Matrix n n ℝ) =
        randomWalkLaplacian S := by
    calc
      ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
          similaritySymmetrizedLaplacian S * (u : Matrix n n ℝ) =
          ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ) *
            ((u : Matrix n n ℝ) * randomWalkLaplacian S *
              ((u⁻¹ : (Matrix n n ℝ)ˣ) : Matrix n n ℝ)) *
                (u : Matrix n n ℝ) := by
        rw [hconj]
      _ = randomWalkLaplacian S := by
        simp [Matrix.mul_assoc]
  have hrw_zero : randomWalkLaplacian S = 0 := by
    rw [← hback]
    simp [hsym_zero]
  exact hrw_ne hrw_zero

lemma randomWalkLaplacian_exists_nonzero_spectral_value_of_constant_kernel
    (S : Matrix n n ℝ) [Nontrivial n] (hsymm : S.IsSymm)
    (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    (hker : ∀ x : n → ℝ,
      (randomWalkLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (randomWalkLaplacian S) ∧ μ ≠ 0 := by
  have hrw_ne : randomWalkLaplacian S ≠ 0 :=
    matrix_ne_zero_of_constant_kernel (randomWalkLaplacian S) hker
  have hsym_ne : similaritySymmetrizedLaplacian S ≠ 0 :=
    similaritySymmetrizedLaplacian_ne_zero_of_randomWalkLaplacian_ne_zero
      S hpos hrw_ne
  have hherm := (similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg).isHermitian
  rcases isHermitian_exists_nonzero_real_spectrum hherm hsym_ne with ⟨μ, hμ, hμne⟩
  have hspectrum := randomWalkLaplacian_spectrum_eq_similaritySymmetrizedLaplacian S hpos
  exact ⟨μ, by simpa [hspectrum] using hμ, hμne⟩

theorem randomWalkLaplacian_cheeger_positive_spectral_gap
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i)
    (C : WeightedCheegerGapCertificate S) :
    ∃ γ : ℝ, γ = C.h0 ^ 2 / 2 ∧ 0 < γ ∧
      ∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), μ ≠ 0 → γ ≤ μ := by
  refine ⟨C.h0 ^ 2 / 2, rfl, cheegerGapValue_pos S C, ?_⟩
  intro μ hμ hne
  have hspectrum := randomWalkLaplacian_spectrum_eq_similaritySymmetrizedLaplacian S hpos
  exact C.spectral_gap_bound μ (by simpa [hspectrum] using hμ) hne

/-- Scalar amplitude of one nonzero spectral mode under heat-flow decay. -/
noncomputable def spectralModeAmplitude (μ t a : ℝ) : ℝ :=
  Real.exp (-μ * t) * a

/-- Quadratic energy of one scalar spectral mode. -/
noncomputable def spectralModeEnergy (μ t a : ℝ) : ℝ :=
  (spectralModeAmplitude μ t a)^ 2

lemma spectralModeEnergy_decay
    {γ μ t a : ℝ} (hμ : γ ≤ μ) (ht : 0 ≤ t) :
    spectralModeEnergy μ t a ≤ Real.exp (-2 * γ * t) * a^ 2 := by
  have hle_exp : Real.exp (-μ * t) ≤ Real.exp (-γ * t) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hsq : (Real.exp (-μ * t))^ 2 ≤ (Real.exp (-γ * t))^ 2 := by
    exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos _)) hle_exp 2
  have hγsq : (Real.exp (-γ * t))^ 2 = Real.exp (-2 * γ * t) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  calc
    spectralModeEnergy μ t a = (Real.exp (-μ * t))^ 2 * a^ 2 := by
      simp [spectralModeEnergy, spectralModeAmplitude]
      ring
    _ ≤ (Real.exp (-γ * t))^ 2 * a^ 2 := by
      exact mul_le_mul_of_nonneg_right hsq (sq_nonneg a)
    _ = Real.exp (-2 * γ * t) * a^ 2 := by
      rw [hγsq]

noncomputable def modalEnergy {κ : Type*} [Fintype κ] (a : κ → ℝ) : ℝ :=
  ∑ k, (a k)^ 2

noncomputable def modalDirichletEnergy {κ : Type*} [Fintype κ]
    (μ : κ → ℝ) (a : κ → ℝ) : ℝ :=
  ∑ k, μ k * (a k)^ 2

noncomputable def modalHeatEnergy {κ : Type*} [Fintype κ]
    (μ : κ → ℝ) (t : ℝ) (a : κ → ℝ) : ℝ :=
  ∑ k, spectralModeEnergy (μ k) t (a k)

def ReducedModalCoefficients {κ : Type*} (μ : κ → ℝ) (a : κ → ℝ) : Prop :=
  ∀ k, μ k = 0 → a k = 0

lemma modal_poincare
    {κ : Type*} [Fintype κ] {γ : ℝ} {μ : κ → ℝ} {a : κ → ℝ}
    (hreduced : ReducedModalCoefficients μ a)
    (hgap : ∀ k, μ k ≠ 0 → γ ≤ μ k) :
    γ * modalEnergy a ≤ modalDirichletEnergy μ a := by
  rw [modalEnergy, modalDirichletEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k _
  by_cases hμ0 : μ k = 0
  · have ha0 : a k = 0 := hreduced k hμ0
    simp [hμ0, ha0]
  · exact mul_le_mul_of_nonneg_right (hgap k hμ0) (sq_nonneg (a k))

lemma modal_heat_energy_decay
    {κ : Type*} [Fintype κ] {γ t : ℝ} {μ : κ → ℝ} {a : κ → ℝ}
    (hreduced : ReducedModalCoefficients μ a)
    (hgap : ∀ k, μ k ≠ 0 → γ ≤ μ k) (ht : 0 ≤ t) :
    modalHeatEnergy μ t a ≤ Real.exp (-2 * γ * t) * modalEnergy a := by
  rw [modalHeatEnergy, modalEnergy, Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro k _
  by_cases hμ0 : μ k = 0
  · have ha0 : a k = 0 := hreduced k hμ0
    simp [spectralModeEnergy, spectralModeAmplitude, hμ0, ha0]
  · exact spectralModeEnergy_decay (hgap k hμ0) ht

/-- Diagonal heat flow on finite spectral-coordinate vectors. -/
noncomputable def diagonalHeatFlow {κ : Type*}
    (μ : κ → ℝ) (t : ℝ) (a : κ → ℝ) : κ → ℝ :=
  fun k => spectralModeAmplitude (μ k) t (a k)

@[simp] lemma diagonalHeatFlow_zero_time {κ : Type*}
    (μ : κ → ℝ) (a : κ → ℝ) :
    diagonalHeatFlow μ 0 a = a := by
  funext k
  simp [diagonalHeatFlow, spectralModeAmplitude]

lemma diagonalHeatFlow_add_time {κ : Type*}
    (μ : κ → ℝ) (s t : ℝ) (a : κ → ℝ) :
    diagonalHeatFlow μ (s + t) a =
      diagonalHeatFlow μ s (diagonalHeatFlow μ t a) := by
  funext k
  unfold diagonalHeatFlow spectralModeAmplitude
  have harg : -(μ k) * (s + t) = -(μ k) * s + -(μ k) * t := by ring
  rw [harg, Real.exp_add]
  ring

lemma modalEnergy_diagonalHeatFlow
    {κ : Type*} [Fintype κ] (μ : κ → ℝ) (t : ℝ) (a : κ → ℝ) :
    modalEnergy (diagonalHeatFlow μ t a) = modalHeatEnergy μ t a := by
  simp [modalEnergy, modalHeatEnergy, diagonalHeatFlow, spectralModeEnergy]

lemma reducedModalCoefficients_diagonalHeatFlow
    {κ : Type*} {μ : κ → ℝ} {a : κ → ℝ}
    (hreduced : ReducedModalCoefficients μ a) (t : ℝ) :
    ReducedModalCoefficients μ (diagonalHeatFlow μ t a) := by
  intro k hμ0
  change spectralModeAmplitude (μ k) t (a k) = 0
  rw [hreduced k hμ0]
  simp [spectralModeAmplitude]

lemma diagonalHeatFlow_energy_decay
    {κ : Type*} [Fintype κ] {γ t : ℝ} {μ : κ → ℝ} {a : κ → ℝ}
    (hreduced : ReducedModalCoefficients μ a)
    (hgap : ∀ k, μ k ≠ 0 → γ ≤ μ k) (ht : 0 ≤ t) :
    modalEnergy (diagonalHeatFlow μ t a) ≤
      Real.exp (-2 * γ * t) * modalEnergy a := by
  rw [modalEnergy_diagonalHeatFlow]
  exact modal_heat_energy_decay hreduced hgap ht

/-- A finite real spectral frame for a matrix acting on Euclidean coordinates. -/
structure MatrixSpectralFrame {ι : Type*} [Fintype ι]
    (A : Matrix ι ι ℝ) (κ : Type*) [Fintype κ] where
  basis : OrthonormalBasis κ ℝ (EuclideanSpace ℝ ι)
  freq : κ → ℝ
  eigen_mulVec : ∀ k, A.mulVec (basis k).ofLp = fun i => freq k * (basis k).ofLp i

namespace MatrixSpectralFrame

noncomputable def coords {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (x : EuclideanSpace ℝ ι) : κ → ℝ :=
  (F.basis.repr x).ofLp

noncomputable def heatFlow {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (t : ℝ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ ι :=
  F.basis.repr.symm (WithLp.toLp 2 (diagonalHeatFlow F.freq t (F.coords x)))

@[simp] lemma coords_heatFlow {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (t : ℝ) (x : EuclideanSpace ℝ ι) :
    F.coords (F.heatFlow t x) = diagonalHeatFlow F.freq t (F.coords x) := by
  unfold coords heatFlow
  rw [LinearIsometryEquiv.apply_symm_apply]
  rfl

@[simp] lemma heatFlow_zero_time {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (x : EuclideanSpace ℝ ι) :
    F.heatFlow 0 x = x := by
  unfold heatFlow coords
  simp

lemma heatFlow_add_time {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (s t : ℝ) (x : EuclideanSpace ℝ ι) :
    F.heatFlow (s + t) x = F.heatFlow s (F.heatFlow t x) := by
  apply F.basis.repr.injective
  ext k
  change F.coords (F.heatFlow (s + t) x) k =
    F.coords (F.heatFlow s (F.heatFlow t x)) k
  rw [coords_heatFlow, coords_heatFlow, coords_heatFlow, diagonalHeatFlow_add_time]

lemma modalEnergy_coords_eq_norm_sq {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (x : EuclideanSpace ℝ ι) :
    modalEnergy (F.coords x) = ‖x‖ ^ 2 := by
  have hcoords := EuclideanSpace.real_norm_sq_eq (F.basis.repr x)
  have hnorm : ‖F.basis.repr x‖ = ‖x‖ := F.basis.repr.norm_map x
  rw [modalEnergy]
  simp only [coords]
  rw [← hcoords]
  rw [hnorm]

lemma heatFlow_energy_eq_modal {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    (t : ℝ) (x : EuclideanSpace ℝ ι) :
    ‖F.heatFlow t x‖ ^ 2 = modalEnergy (diagonalHeatFlow F.freq t (F.coords x)) := by
  unfold heatFlow
  have hnorm :
      ‖F.basis.repr.symm
        (WithLp.toLp 2 (diagonalHeatFlow F.freq t (F.coords x)))‖ =
        ‖(WithLp.toLp 2
          (diagonalHeatFlow F.freq t (F.coords x)) : EuclideanSpace ℝ κ)‖ :=
    F.basis.repr.symm.norm_map
      (WithLp.toLp 2 (diagonalHeatFlow F.freq t (F.coords x)))
  rw [hnorm]
  rw [modalEnergy]
  simpa using (EuclideanSpace.real_norm_sq_eq
    (WithLp.toLp 2 (diagonalHeatFlow F.freq t (F.coords x)) : EuclideanSpace ℝ κ))

lemma heatFlow_energy_decay {ι κ : Type*} [Fintype ι] [Fintype κ]
    {A : Matrix ι ι ℝ} (F : MatrixSpectralFrame A κ)
    {γ t : ℝ} {x : EuclideanSpace ℝ ι}
    (hreduced : ReducedModalCoefficients F.freq (F.coords x))
    (hgap : ∀ k, F.freq k ≠ 0 → γ ≤ F.freq k) (ht : 0 ≤ t) :
    ‖F.heatFlow t x‖ ^ 2 ≤ Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  rw [F.heatFlow_energy_eq_modal]
  rw [← F.modalEnergy_coords_eq_norm_sq x]
  exact diagonalHeatFlow_energy_decay hreduced hgap ht

end MatrixSpectralFrame

/-- The canonical Mathlib spectral frame attached to a finite Hermitian real matrix. -/
noncomputable def hermitianSpectralFrame
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : MatrixSpectralFrame A ι where
  basis := hA.eigenvectorBasis
  freq := hA.eigenvalues
  eigen_mulVec := by
    intro k
    simpa [Pi.smul_apply, smul_eq_mul] using hA.mulVec_eigenvectorBasis k

lemma hermitianSpectralFrame_freq_mem_spectrum
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    ∀ k, (hermitianSpectralFrame hA).freq k ∈ spectrum ℝ A := by
  intro k
  exact hA.eigenvalues_mem_spectrum_real k

theorem posSemidef_hermitianSpectralFrame_heatFlow_decay
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ ι,
        ReducedModalCoefficients
          (hermitianSpectralFrame hA.isHermitian).freq
          ((hermitianSpectralFrame hA.isHermitian).coords x) →
          γ * modalEnergy ((hermitianSpectralFrame hA.isHermitian).coords x) ≤
              modalDirichletEnergy
                (hermitianSpectralFrame hA.isHermitian).freq
                ((hermitianSpectralFrame hA.isHermitian).coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖(hermitianSpectralFrame hA.isHermitian).heatFlow t x‖ ^ 2 ≤
                Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  let F := hermitianSpectralFrame hA.isHermitian
  have hnonneg : ∀ μ ∈ spectrum ℝ A, 0 ≤ μ := by
    intro μ hμ
    rw [hA.isHermitian.spectrum_real_eq_range_eigenvalues] at hμ
    rcases hμ with ⟨i, rfl⟩
    exact hA.eigenvalues_nonneg i
  rcases finite_nonzero_spectral_gap (A.finite_real_spectrum) hnonneg with
    ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro x hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced
      (fun k hne => hgap (F.freq k)
        (hermitianSpectralFrame_freq_mem_spectrum hA.isHermitian k) hne)
  · intro t ht
    exact F.heatFlow_energy_decay hreduced
      (fun k hne => hgap (F.freq k)
        (hermitianSpectralFrame_freq_mem_spectrum hA.isHermitian k) hne) ht

theorem randomWalkLaplacian_modal_poincare_decay
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ (randomWalkLaplacian S)) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalHeatEnergy μ t a ≤ Real.exp (-2 * γ * t) * modalEnergy a := by
  rcases randomWalkLaplacian_positive_spectral_gap S hsymm hnonneg hpos with
    ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro a hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (μ k) (hspec k) hne)
  · intro t ht
    exact modal_heat_energy_decay hreduced
      (fun k hne => hgap (μ k) (hspec k) hne) ht

theorem randomWalkLaplacian_diagonalHeatFlow_decay
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ (randomWalkLaplacian S)) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalEnergy (diagonalHeatFlow μ t a) ≤
              Real.exp (-2 * γ * t) * modalEnergy a := by
  rcases randomWalkLaplacian_positive_spectral_gap S hsymm hnonneg hpos with
    ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro a hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (μ k) (hspec k) hne)
  · intro t ht
    exact diagonalHeatFlow_energy_decay hreduced
      (fun k hne => hgap (μ k) (hspec k) hne) ht

theorem randomWalkLaplacian_cheeger_diagonalHeatFlow_decay
    (S : Matrix n n ℝ) (hpos : ∀ i, 0 < blockDegree S i)
    (C : WeightedCheegerGapCertificate S)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ (randomWalkLaplacian S)) :
    0 < C.h0 ^ 2 / 2 ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        (C.h0 ^ 2 / 2) * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalEnergy (diagonalHeatFlow μ t a) ≤
              Real.exp (-2 * (C.h0 ^ 2 / 2) * t) * modalEnergy a := by
  refine ⟨cheegerGapValue_pos S C, ?_⟩
  intro a hreduced
  have hgap : ∀ k, μ k ≠ 0 → C.h0 ^ 2 / 2 ≤ μ k := by
    intro k hne
    have hspectrum := randomWalkLaplacian_spectrum_eq_similaritySymmetrizedLaplacian S hpos
    exact C.spectral_gap_bound (μ k) (by simpa [hspectrum] using hspec k) hne
  refine ⟨modal_poincare hreduced hgap, ?_⟩
  intro t ht
  exact diagonalHeatFlow_energy_decay hreduced hgap ht

/-- Real-valued unweighted cut count for a fixed adjacency pattern. -/
def unweightedCutWeight (Adj : n → n → Prop) [DecidableRel Adj]
    (U : Finset n) : ℝ :=
  U.sum fun i => ((Finset.univ : Finset n) \ U).sum fun j =>
    if Adj i j then (1 : ℝ) else 0

/-- Unweighted Cheeger lower bound written without division. -/
def UnweightedCheegerLowerBound (Adj : n → n → Prop) [DecidableRel Adj]
    (h : ℝ) : Prop :=
  ∀ U : Finset n,
    U.Nonempty → 2 * U.card ≤ Fintype.card n →
      h * (U.card : ℝ) ≤ unweightedCutWeight Adj U

lemma cutWeight_le_weightedCut
    (S : Matrix n n ℝ) (Adj : n → n → Prop) [DecidableRel Adj]
    {cStar : ℝ}
    (hnonneg : ∀ i j, 0 ≤ S i j)
    (hedge : ∀ i j, Adj i j → cStar ≤ S i j)
    (U : Finset n) :
    cStar * unweightedCutWeight Adj U ≤ weightedCut S U := by
  rw [unweightedCutWeight, weightedCut]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro i hi
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum ?_
  intro j hj
  by_cases hadj : Adj i j
  · simp [hadj, hedge i j hadj]
  · simp [hadj, hnonneg i j]

omit [DecidableEq n] in
lemma weightedVolume_le_card_mul_degree_bound
    (S : Matrix n n ℝ) {dMax : ℝ}
    (hdegree : ∀ i, blockDegree S i ≤ dMax)
    (U : Finset n) :
    weightedVolume S U ≤ dMax * (U.card : ℝ) := by
  rw [weightedVolume]
  calc
    U.sum (fun i => blockDegree S i) ≤ U.sum (fun _ => dMax) := by
      exact Finset.sum_le_sum (fun i _ => hdegree i)
    _ = dMax * (U.card : ℝ) := by simp [mul_comm]

lemma weightedCheegerLowerBound_of_unweighted
    (S : Matrix n n ℝ) (Adj : n → n → Prop) [DecidableRel Adj]
    {cStar dMax hUnweighted : ℝ}
    (hcStar_nonneg : 0 ≤ cStar)
    (hdMax_pos : 0 < dMax)
    (hhUnweighted_nonneg : 0 ≤ hUnweighted)
    (hnonneg : ∀ i j, 0 ≤ S i j)
    (hedge : ∀ i j, Adj i j → cStar ≤ S i j)
    (hdegree : ∀ i, blockDegree S i ≤ dMax)
    (hunweighted : UnweightedCheegerLowerBound Adj hUnweighted) :
    WeightedCheegerLowerBound S (cStar / dMax * hUnweighted) := by
  intro U hUne hUhalf
  have hvol := weightedVolume_le_card_mul_degree_bound S hdegree U
  have hcut := cutWeight_le_weightedCut S Adj hnonneg hedge U
  have hunw := hunweighted U hUne hUhalf
  have hscale_nonneg : 0 ≤ cStar / dMax * hUnweighted := by positivity
  calc
    (cStar / dMax * hUnweighted) * weightedVolume S U
        ≤ (cStar / dMax * hUnweighted) * (dMax * (U.card : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hvol hscale_nonneg
    _ = cStar * (hUnweighted * (U.card : ℝ)) := by
          field_simp [ne_of_gt hdMax_pos]
    _ ≤ cStar * unweightedCutWeight Adj U := by
          exact mul_le_mul_of_nonneg_left hunw hcStar_nonneg
    _ ≤ weightedCut S U := hcut

/-- Uniform Cheeger certificate for a family of refined overlap matrices. -/
structure UniformCheegerGapCertificate {α : Type*}
    (S : α → Matrix n n ℝ) where
  h0 : ℝ
  h0_pos : 0 < h0
  lower_bound : ∀ m, WeightedCheegerLowerBound (S m) h0
  spectral_gap_bound :
    ∀ m μ, μ ∈ spectrum ℝ (similaritySymmetrizedLaplacian (S m)) →
      μ ≠ 0 → h0 ^ 2 / 2 ≤ μ

def UniformCheegerGapCertificate.to_single {α : Type*}
    {S : α → Matrix n n ℝ} (C : UniformCheegerGapCertificate S) (m : α) :
    WeightedCheegerGapCertificate (S m) where
  h0 := C.h0
  h0_pos := C.h0_pos
  lower_bound := C.lower_bound m
  spectral_gap_bound := C.spectral_gap_bound m

theorem uniformCheeger_randomWalkLaplacian_positive_spectral_gap {α : Type*}
    (S : α → Matrix n n ℝ) (hpos : ∀ m i, 0 < blockDegree (S m) i)
    (C : UniformCheegerGapCertificate S) (m : α) :
    ∃ γ : ℝ, γ = C.h0 ^ 2 / 2 ∧ 0 < γ ∧
      ∀ μ ∈ spectrum ℝ (randomWalkLaplacian (S m)), μ ≠ 0 → γ ≤ μ := by
  simpa using
    randomWalkLaplacian_cheeger_positive_spectral_gap (S m) (hpos m)
      (C.to_single m)

theorem uniformCheeger_randomWalkLaplacian_diagonalHeatFlow_decay {α : Type*}
    (S : α → Matrix n n ℝ) (hpos : ∀ m i, 0 < blockDegree (S m) i)
    (C : UniformCheegerGapCertificate S) (m : α)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ (randomWalkLaplacian (S m))) :
    0 < C.h0 ^ 2 / 2 ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        (C.h0 ^ 2 / 2) * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalEnergy (diagonalHeatFlow μ t a) ≤
              Real.exp (-2 * (C.h0 ^ 2 / 2) * t) * modalEnergy a := by
  simpa using
    randomWalkLaplacian_cheeger_diagonalHeatFlow_decay (S m) (hpos m)
      (C.to_single m) μ hspec

/--
Shape-regular refinement data implying a uniform Cheeger gap, modulo the
standard Cheeger inequality for the symmetric normalised Laplacian.
-/
structure ShapeRegularRefinementCheegerCertificate {α : Type*}
    (S : α → Matrix n n ℝ) (Adj : n → n → Prop) [DecidableRel Adj] where
  cStar : ℝ
  dMax : ℝ
  hUnweighted : ℝ
  cStar_pos : 0 < cStar
  dMax_pos : 0 < dMax
  hUnweighted_pos : 0 < hUnweighted
  weights_nonneg : ∀ m i j, 0 ≤ S m i j
  edge_weight_lower : ∀ m i j, Adj i j → cStar ≤ S m i j
  degree_upper : ∀ m i, blockDegree (S m) i ≤ dMax
  unweighted_lower : UnweightedCheegerLowerBound Adj hUnweighted
  spectral_gap_bound :
    ∀ m μ, μ ∈ spectrum ℝ (similaritySymmetrizedLaplacian (S m)) →
      μ ≠ 0 → (cStar / dMax * hUnweighted) ^ 2 / 2 ≤ μ

lemma ShapeRegularRefinementCheegerCertificate.h0_pos {α : Type*}
    {S : α → Matrix n n ℝ} {Adj : n → n → Prop} [DecidableRel Adj]
    (C : ShapeRegularRefinementCheegerCertificate S Adj) :
    0 < C.cStar / C.dMax * C.hUnweighted := by
  exact mul_pos (div_pos C.cStar_pos C.dMax_pos) C.hUnweighted_pos

lemma ShapeRegularRefinementCheegerCertificate.lower_bound {α : Type*}
    {S : α → Matrix n n ℝ} {Adj : n → n → Prop} [DecidableRel Adj]
    (C : ShapeRegularRefinementCheegerCertificate S Adj) (m : α) :
    WeightedCheegerLowerBound (S m) (C.cStar / C.dMax * C.hUnweighted) := by
  exact weightedCheegerLowerBound_of_unweighted (S m) Adj
    (le_of_lt C.cStar_pos) C.dMax_pos (le_of_lt C.hUnweighted_pos)
    (C.weights_nonneg m) (C.edge_weight_lower m) (C.degree_upper m)
    C.unweighted_lower

noncomputable def ShapeRegularRefinementCheegerCertificate.uniformCertificate
    {α : Type*} {S : α → Matrix n n ℝ} {Adj : n → n → Prop}
    [DecidableRel Adj]
    (C : ShapeRegularRefinementCheegerCertificate S Adj) :
    UniformCheegerGapCertificate S where
  h0 := C.cStar / C.dMax * C.hUnweighted
  h0_pos := C.h0_pos
  lower_bound := C.lower_bound
  spectral_gap_bound := C.spectral_gap_bound

theorem shapeRegularRefinement_uniform_positive_spectral_gap {α : Type*}
    (S : α → Matrix n n ℝ) (Adj : n → n → Prop) [DecidableRel Adj]
    (hpos : ∀ m i, 0 < blockDegree (S m) i)
    (C : ShapeRegularRefinementCheegerCertificate S Adj) (m : α) :
    ∃ γ : ℝ,
      γ = (C.cStar / C.dMax * C.hUnweighted) ^ 2 / 2 ∧ 0 < γ ∧
        ∀ μ ∈ spectrum ℝ (randomWalkLaplacian (S m)), μ ≠ 0 → γ ≤ μ := by
  exact uniformCheeger_randomWalkLaplacian_positive_spectral_gap S hpos
    C.uniformCertificate m

/-- Exact inverse-square profile in the coarse box size. -/
noncomputable def inverseSquareProfile (coefficient : ℝ) (L : ℕ) : ℝ :=
  coefficient / (L : ℝ) ^ 2

/-- Eventual two-sided inverse-square spectral scaling. -/
structure InverseSquareSpectralScaling (lambda : ℕ → ℝ) where
  L0 : ℕ
  L0_pos : 0 < L0
  lowerCoeff : ℝ
  upperCoeff : ℝ
  lowerCoeff_pos : 0 < lowerCoeff
  upperCoeff_pos : 0 < upperCoeff
  bounds :
    ∀ L, L0 ≤ L →
      lowerCoeff / (L : ℝ) ^ 2 ≤ lambda L ∧
        lambda L ≤ upperCoeff / (L : ℝ) ^ 2

lemma InverseSquareSpectralScaling.lambda_pos {lambda : ℕ → ℝ}
    (C : InverseSquareSpectralScaling lambda) :
    ∀ L, C.L0 ≤ L → 0 < lambda L := by
  intro L hL
  have hLposNat : 0 < L := lt_of_lt_of_le C.L0_pos hL
  have hLsqpos : 0 < (L : ℝ) ^ 2 := by
    exact sq_pos_of_ne_zero (ne_of_gt (Nat.cast_pos.mpr hLposNat))
  have hlower : 0 < C.lowerCoeff / (L : ℝ) ^ 2 :=
    div_pos C.lowerCoeff_pos hLsqpos
  exact lt_of_lt_of_le hlower (C.bounds L hL).1

/-- Rescaled spectral value `L^ 2 λ(L)`. -/
noncomputable def rescaledSpectralValue (lambda : ℕ → ℝ) (L : ℕ) : ℝ :=
  (L : ℝ) ^ 2 * lambda L

lemma rescaled_sub_coefficient_eq_mul_sub_inverseSquareProfile
    {lambda : ℕ → ℝ} {coefficient : ℝ} {L : ℕ} (hL : L ≠ 0) :
    rescaledSpectralValue lambda L - coefficient =
      (L : ℝ) ^ 2 * (lambda L - inverseSquareProfile coefficient L) := by
  unfold rescaledSpectralValue inverseSquareProfile
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hL
  have hsq : (L : ℝ) ^ 2 ≠ 0 := pow_ne_zero 2 hLreal
  field_simp [hsq]

lemma rescaled_abs_error_le_of_cubic_eigenvalue_error
    {lambda : ℕ → ℝ} {coefficient K : ℝ} {L : ℕ}
    (hL : 0 < L)
    (habs : |lambda L - inverseSquareProfile coefficient L| ≤
      K / (L : ℝ) ^ 3) :
    |rescaledSpectralValue lambda L - coefficient| ≤ K / (L : ℝ) := by
  have hLne : L ≠ 0 := Nat.ne_of_gt hL
  have hLreal : (L : ℝ) ≠ 0 := by exact_mod_cast hLne
  have hLsqnonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  rw [rescaled_sub_coefficient_eq_mul_sub_inverseSquareProfile hLne]
  rw [abs_mul, abs_of_nonneg hLsqnonneg]
  have hmul := mul_le_mul_of_nonneg_left habs hLsqnonneg
  refine hmul.trans_eq ?_
  field_simp [hLreal]

/-- Positive homogenization-type limit certificate for inverse-square spectral scaling. -/
structure RescaledInverseSquareLimitCertificate (lambda : ℕ → ℝ) where
  coefficient : ℝ
  coefficient_pos : 0 < coefficient
  tendsto_rescaled :
    Filter.Tendsto (fun L : ℕ => rescaledSpectralValue lambda L)
      Filter.atTop (nhds coefficient)

noncomputable def inverseSquareSpectralScaling_of_rescaled_tendsto
    {lambda : ℕ → ℝ}
    (C : RescaledInverseSquareLimitCertificate lambda) :
    InverseSquareSpectralScaling lambda := by
  have hlow_lt : C.coefficient / 2 < C.coefficient := by nlinarith [C.coefficient_pos]
  have hhigh_lt : C.coefficient < 2 * C.coefficient := by nlinarith [C.coefficient_pos]
  have hnear : Set.Ioo (C.coefficient / 2) (2 * C.coefficient) ∈ nhds C.coefficient := by
    exact Ioo_mem_nhds hlow_lt hhigh_lt
  have hev : ∀ᶠ L in Filter.atTop,
      rescaledSpectralValue lambda L ∈ Set.Ioo (C.coefficient / 2) (2 * C.coefficient) :=
    C.tendsto_rescaled.eventually hnear
  let N := Classical.choose (Filter.eventually_atTop.mp hev)
  have hN : ∀ L ≥ N,
      rescaledSpectralValue lambda L ∈ Set.Ioo (C.coefficient / 2) (2 * C.coefficient) :=
    Classical.choose_spec (Filter.eventually_atTop.mp hev)
  refine
    { L0 := max N 1
      L0_pos := ?_
      lowerCoeff := C.coefficient / 2
      upperCoeff := 2 * C.coefficient
      lowerCoeff_pos := by nlinarith [C.coefficient_pos]
      upperCoeff_pos := by nlinarith [C.coefficient_pos]
      bounds := ?_ }
  · exact lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_right N 1)
  · intro L hL
    have hNle : N ≤ L := le_trans (Nat.le_max_left N 1) hL
    have hOne : 1 ≤ L := le_trans (Nat.le_max_right N 1) hL
    have hLposNat : 0 < L := lt_of_lt_of_le Nat.zero_lt_one hOne
    have hden_pos : 0 < (L : ℝ) ^ 2 :=
      sq_pos_of_ne_zero (ne_of_gt (Nat.cast_pos.mpr hLposNat))
    have hinterval := hN L hNle
    have hlo_rescaled : C.coefficient / 2 ≤ rescaledSpectralValue lambda L :=
      le_of_lt hinterval.1
    have hhi_rescaled : rescaledSpectralValue lambda L ≤ 2 * C.coefficient :=
      le_of_lt hinterval.2
    constructor
    · exact (div_le_iff₀ hden_pos).mpr (by
        simpa [rescaledSpectralValue, mul_comm, mul_left_comm, mul_assoc] using hlo_rescaled)
    · exact (le_div_iff₀ hden_pos).mpr (by
        simpa [rescaledSpectralValue, mul_comm, mul_left_comm, mul_assoc] using hhi_rescaled)

noncomputable def exact_inverseSquareSpectralScaling
    {lambda : ℕ → ℝ} {coefficient : ℝ} (hcoeff : 0 < coefficient)
    {L0 : ℕ} (hL0 : 0 < L0)
    (hexact : ∀ L, L0 ≤ L → lambda L = inverseSquareProfile coefficient L) :
    InverseSquareSpectralScaling lambda where
  L0 := L0
  L0_pos := hL0
  lowerCoeff := coefficient
  upperCoeff := coefficient
  lowerCoeff_pos := hcoeff
  upperCoeff_pos := hcoeff
  bounds := by
    intro L hL
    rw [hexact L hL, inverseSquareProfile]
    exact ⟨le_rfl, le_rfl⟩

/-- Spectral continuum open-boundary coefficient for an isotropic effective diffusivity. -/
noncomputable def openSpectralContinuumCoefficient (D_eff : ℝ) : ℝ :=
  Real.pi ^ 2 * D_eff

/-- Spectral continuum periodic coefficient for an isotropic effective diffusivity. -/
noncomputable def periodicSpectralContinuumCoefficient (D_eff : ℝ) : ℝ :=
  4 * Real.pi ^ 2 * D_eff

lemma openSpectralContinuumCoefficient_pos {D_eff : ℝ} (hD : 0 < D_eff) :
    0 < openSpectralContinuumCoefficient D_eff := by
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero (ne_of_gt Real.pi_pos)
  exact mul_pos hpi2 hD

lemma periodicSpectralContinuumCoefficient_pos {D_eff : ℝ} (hD : 0 < D_eff) :
    0 < periodicSpectralContinuumCoefficient D_eff := by
  have hpi2 : 0 < Real.pi ^ 2 := sq_pos_of_ne_zero (ne_of_gt Real.pi_pos)
  exact mul_pos (mul_pos (by norm_num) hpi2) hD

lemma periodicSpectralContinuumCoefficient_eq_four_open (D_eff : ℝ) :
    periodicSpectralContinuumCoefficient D_eff =
      4 * openSpectralContinuumCoefficient D_eff := by
  unfold periodicSpectralContinuumCoefficient openSpectralContinuumCoefficient
  ring

/-- Open-boundary inverse-square spectral continuum profile. -/
noncomputable def openSpectralContinuumProfile (D_eff : ℝ) : ℕ → ℝ :=
  inverseSquareProfile (openSpectralContinuumCoefficient D_eff)

/-- Periodic inverse-square spectral continuum profile. -/
noncomputable def periodicSpectralContinuumProfile (D_eff : ℝ) : ℕ → ℝ :=
  inverseSquareProfile (periodicSpectralContinuumCoefficient D_eff)

noncomputable def openSpectralContinuum_inverseSquareScaling {D_eff : ℝ}
    (hD : 0 < D_eff) {L0 : ℕ} (hL0 : 0 < L0) :
    InverseSquareSpectralScaling (openSpectralContinuumProfile D_eff) :=
  exact_inverseSquareSpectralScaling (openSpectralContinuumCoefficient_pos hD) hL0
    (by intro L hL; rfl)

noncomputable def periodicSpectralContinuum_inverseSquareScaling {D_eff : ℝ}
    (hD : 0 < D_eff) {L0 : ℕ} (hL0 : 0 < L0) :
    InverseSquareSpectralScaling (periodicSpectralContinuumProfile D_eff) :=
  exact_inverseSquareSpectralScaling (periodicSpectralContinuumCoefficient_pos hD) hL0
    (by intro L hL; rfl)

/-- Boundary difference is inverse-square bounded. -/
def BoundaryDifferenceInverseSquareBound
    (periodicLambda openLambda : ℕ → ℝ) (K : ℝ) (L0 : ℕ) : Prop :=
  ∀ L, L0 ≤ L →
    |periodicLambda L - openLambda L| ≤ K / (L : ℝ) ^ 2

lemma exactContinuum_boundaryDifferenceInverseSquareBound {D_eff : ℝ}
    (hD : 0 < D_eff) {L0 : ℕ} :
    BoundaryDifferenceInverseSquareBound
      (periodicSpectralContinuumProfile D_eff)
      (openSpectralContinuumProfile D_eff)
      (3 * Real.pi ^ 2 * D_eff) L0 := by
  intro L hL
  unfold periodicSpectralContinuumProfile openSpectralContinuumProfile
    inverseSquareProfile periodicSpectralContinuumCoefficient openSpectralContinuumCoefficient
  have hKnonneg : 0 ≤ 3 * Real.pi ^ 2 * D_eff := by positivity
  have hdennonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  have hnonneg : 0 ≤ (3 * Real.pi ^ 2 * D_eff) / (L : ℝ) ^ 2 :=
    div_nonneg hKnonneg hdennonneg
  have hdiff :
      4 * Real.pi ^ 2 * D_eff / (L : ℝ) ^ 2 -
        Real.pi ^ 2 * D_eff / (L : ℝ) ^ 2 =
          (3 * Real.pi ^ 2 * D_eff) / (L : ℝ) ^ 2 := by
    ring
  rw [hdiff]
  rw [abs_of_nonneg hnonneg]

/-- Homogenization-limit certificate for the open/periodic boundary pair. -/
structure BoundaryContinuumLimitCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic_tendsto_rescaled :
    Filter.Tendsto (fun L : ℕ => rescaledSpectralValue periodicLambda L)
      Filter.atTop (nhds (periodicSpectralContinuumCoefficient D_eff))
  open_tendsto_rescaled :
    Filter.Tendsto (fun L : ℕ => rescaledSpectralValue openLambda L)
      Filter.atTop (nhds (openSpectralContinuumCoefficient D_eff))

/--
Error-form continuum certificate.  This is the usual analytic target for a
homogenization proof: after multiplying the selected eigenvalue by `L^ 2`, the
error against the continuum coefficient tends to zero.
-/
structure BoundaryContinuumErrorCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic_rescaled_error_tendsto_zero :
    Filter.Tendsto
      (fun L : ℕ => rescaledSpectralValue periodicLambda L -
        periodicSpectralContinuumCoefficient D_eff)
      Filter.atTop (nhds 0)
  open_rescaled_error_tendsto_zero :
    Filter.Tendsto
      (fun L : ℕ => rescaledSpectralValue openLambda L -
        openSpectralContinuumCoefficient D_eff)
      Filter.atTop (nhds 0)

namespace BoundaryContinuumErrorCertificate

noncomputable def toLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumErrorCertificate periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic_tendsto_rescaled := by
    have h := C.periodic_rescaled_error_tendsto_zero.add
      (tendsto_const_nhds (x := periodicSpectralContinuumCoefficient C.D_eff))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h
  open_tendsto_rescaled := by
    have h := C.open_rescaled_error_tendsto_zero.add
      (tendsto_const_nhds (x := openSpectralContinuumCoefficient C.D_eff))
    simpa [sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using h

end BoundaryContinuumErrorCertificate

/--
Absolute-error continuum certificate.  This is a standard estimate-level
input: each rescaled eigenvalue differs from its continuum coefficient by an
eventual error bound which tends to zero.
-/
structure BoundaryContinuumAbsErrorBoundCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodicErrorBound : ℕ → ℝ
  openErrorBound : ℕ → ℝ
  periodicErrorBound_tendsto_zero :
    Filter.Tendsto periodicErrorBound Filter.atTop (nhds 0)
  openErrorBound_tendsto_zero :
    Filter.Tendsto openErrorBound Filter.atTop (nhds 0)
  periodic_abs_error_bound :
    ∀ᶠ L in Filter.atTop,
      |rescaledSpectralValue periodicLambda L -
        periodicSpectralContinuumCoefficient D_eff| ≤ periodicErrorBound L
  open_abs_error_bound :
    ∀ᶠ L in Filter.atTop,
      |rescaledSpectralValue openLambda L -
        openSpectralContinuumCoefficient D_eff| ≤ openErrorBound L

namespace BoundaryContinuumAbsErrorBoundCertificate

noncomputable def toError {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda) :
    BoundaryContinuumErrorCertificate periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic_rescaled_error_tendsto_zero := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) C.periodicErrorBound_tendsto_zero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      C.periodic_abs_error_bound
  open_rescaled_error_tendsto_zero := by
    refine (tendsto_zero_iff_abs_tendsto_zero _).2 ?_
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (tendsto_const_nhds (x := (0 : ℝ))) C.openErrorBound_tendsto_zero
      (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      C.open_abs_error_bound

noncomputable def toLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toError.toLimit

end BoundaryContinuumAbsErrorBoundCertificate

/--
Inverse-linear continuum-error certificate.  This packages the common finite
size estimate `|L^ 2 λ_L - C| ≤ K / L`; it implies the absolute-error and
limit-form certificates.
-/
structure BoundaryContinuumInverseLinearErrorBoundCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodicK : ℝ
  periodicK_nonneg : 0 ≤ periodicK
  periodicL0 : ℕ
  openK : ℝ
  openK_nonneg : 0 ≤ openK
  openL0 : ℕ
  periodic_abs_error_bound :
    ∀ L, periodicL0 ≤ L →
      |rescaledSpectralValue periodicLambda L -
        periodicSpectralContinuumCoefficient D_eff| ≤ periodicK / (L : ℝ)
  open_abs_error_bound :
    ∀ L, openL0 ≤ L →
      |rescaledSpectralValue openLambda L -
        openSpectralContinuumCoefficient D_eff| ≤ openK / (L : ℝ)

namespace BoundaryContinuumInverseLinearErrorBoundCertificate

noncomputable def toAbsError {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumInverseLinearErrorBoundCertificate periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodicErrorBound := fun L => C.periodicK / (L : ℝ)
  openErrorBound := fun L => C.openK / (L : ℝ)
  periodicErrorBound_tendsto_zero := by
    simpa using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C.periodicK)
  openErrorBound_tendsto_zero := by
    simpa using
      (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) C.openK)
  periodic_abs_error_bound := by
    filter_upwards [Filter.eventually_ge_atTop C.periodicL0] with L hL
    exact C.periodic_abs_error_bound L hL
  open_abs_error_bound := by
    filter_upwards [Filter.eventually_ge_atTop C.openL0] with L hL
    exact C.open_abs_error_bound L hL

noncomputable def toError {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumInverseLinearErrorBoundCertificate periodicLambda openLambda) :
    BoundaryContinuumErrorCertificate periodicLambda openLambda :=
  C.toAbsError.toError

noncomputable def toLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumInverseLinearErrorBoundCertificate periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toAbsError.toLimit

end BoundaryContinuumInverseLinearErrorBoundCertificate

/--
Cubic eigenvalue-error certificate.  This is an eigenvalue-level finite-size
estimate: the selected eigenvalue is within `K / L^ 3` of the continuum
inverse-square profile.  It implies the inverse-linear rescaled-error
certificate.
-/
structure BoundaryContinuumCubicEigenvalueErrorBoundCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodicK : ℝ
  periodicK_nonneg : 0 ≤ periodicK
  periodicL0 : ℕ
  periodicL0_pos : 0 < periodicL0
  openK : ℝ
  openK_nonneg : 0 ≤ openK
  openL0 : ℕ
  openL0_pos : 0 < openL0
  periodic_abs_eigenvalue_error_bound :
    ∀ L, periodicL0 ≤ L →
      |periodicLambda L - periodicSpectralContinuumProfile D_eff L| ≤
        periodicK / (L : ℝ) ^ 3
  open_abs_eigenvalue_error_bound :
    ∀ L, openL0 ≤ L →
      |openLambda L - openSpectralContinuumProfile D_eff L| ≤
        openK / (L : ℝ) ^ 3

namespace BoundaryContinuumCubicEigenvalueErrorBoundCertificate

noncomputable def toInverseLinear {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      periodicLambda openLambda) :
    BoundaryContinuumInverseLinearErrorBoundCertificate
      periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodicK := C.periodicK
  periodicK_nonneg := C.periodicK_nonneg
  periodicL0 := C.periodicL0
  openK := C.openK
  openK_nonneg := C.openK_nonneg
  openL0 := C.openL0
  periodic_abs_error_bound := by
    intro L hL
    have hLpos : 0 < L := lt_of_lt_of_le C.periodicL0_pos hL
    exact rescaled_abs_error_le_of_cubic_eigenvalue_error
      (lambda := periodicLambda)
      (coefficient := periodicSpectralContinuumCoefficient C.D_eff)
      (K := C.periodicK) hLpos
      (by
        simpa [periodicSpectralContinuumProfile] using
          C.periodic_abs_eigenvalue_error_bound L hL)
  open_abs_error_bound := by
    intro L hL
    have hLpos : 0 < L := lt_of_lt_of_le C.openL0_pos hL
    exact rescaled_abs_error_le_of_cubic_eigenvalue_error
      (lambda := openLambda)
      (coefficient := openSpectralContinuumCoefficient C.D_eff)
      (K := C.openK) hLpos
      (by
        simpa [openSpectralContinuumProfile] using
          C.open_abs_eigenvalue_error_bound L hL)

noncomputable def toAbsError {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda :=
  C.toInverseLinear.toAbsError

noncomputable def toError {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      periodicLambda openLambda) :
    BoundaryContinuumErrorCertificate periodicLambda openLambda :=
  C.toInverseLinear.toError

noncomputable def toLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toInverseLinear.toLimit

end BoundaryContinuumCubicEigenvalueErrorBoundCertificate

namespace BoundaryContinuumLimitCertificate

noncomputable def periodicLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    RescaledInverseSquareLimitCertificate periodicLambda where
  coefficient := periodicSpectralContinuumCoefficient C.D_eff
  coefficient_pos := periodicSpectralContinuumCoefficient_pos C.D_eff_pos
  tendsto_rescaled := C.periodic_tendsto_rescaled

noncomputable def openLimit {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    RescaledInverseSquareLimitCertificate openLambda where
  coefficient := openSpectralContinuumCoefficient C.D_eff
  coefficient_pos := openSpectralContinuumCoefficient_pos C.D_eff_pos
  tendsto_rescaled := C.open_tendsto_rescaled

noncomputable def periodicScaling {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    InverseSquareSpectralScaling periodicLambda :=
  inverseSquareSpectralScaling_of_rescaled_tendsto C.periodicLimit

noncomputable def openScaling {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    InverseSquareSpectralScaling openLambda :=
  inverseSquareSpectralScaling_of_rescaled_tendsto C.openLimit

noncomputable def differenceK {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) : ℝ :=
  C.periodicScaling.upperCoeff + C.openScaling.upperCoeff

noncomputable def differenceL0 {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) : ℕ :=
  max C.periodicScaling.L0 C.openScaling.L0

lemma differenceK_pos {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    0 < C.differenceK := by
  unfold differenceK
  exact add_pos C.periodicScaling.upperCoeff_pos C.openScaling.upperCoeff_pos

theorem boundaryDifferenceInverseSquareBound {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumLimitCertificate periodicLambda openLambda) :
    BoundaryDifferenceInverseSquareBound periodicLambda openLambda
      C.differenceK C.differenceL0 := by
  intro L hL
  have hpL : C.periodicScaling.L0 ≤ L :=
    le_trans (Nat.le_max_left C.periodicScaling.L0 C.openScaling.L0) hL
  have hoL : C.openScaling.L0 ≤ L :=
    le_trans (Nat.le_max_right C.periodicScaling.L0 C.openScaling.L0) hL
  have hp_nonneg : 0 ≤ periodicLambda L :=
    le_of_lt (C.periodicScaling.lambda_pos L hpL)
  have ho_nonneg : 0 ≤ openLambda L :=
    le_of_lt (C.openScaling.lambda_pos L hoL)
  have hp_upper := (C.periodicScaling.bounds L hpL).2
  have ho_upper := (C.openScaling.bounds L hoL).2
  have habs : |periodicLambda L - openLambda L| ≤ periodicLambda L + openLambda L := by
    rw [abs_le]
    constructor <;> nlinarith [hp_nonneg, ho_nonneg]
  have hsum : periodicLambda L + openLambda L ≤ C.differenceK / (L : ℝ) ^ 2 := by
    calc
      periodicLambda L + openLambda L ≤
          C.periodicScaling.upperCoeff / (L : ℝ) ^ 2 +
            C.openScaling.upperCoeff / (L : ℝ) ^ 2 :=
        add_le_add hp_upper ho_upper
      _ = C.differenceK / (L : ℝ) ^ 2 := by
        unfold differenceK
        ring
  exact le_trans habs hsum

end BoundaryContinuumLimitCertificate

/-- A reusable finite matrix family indexed by the coarse scale. -/
structure BoundaryLaplacianFamily where
  Node : ℕ → Type*
  nodeFintype : ∀ L, Fintype (Node L)
  nodeDecidableEq : ∀ L, DecidableEq (Node L)
  laplacian : ∀ L, Matrix (Node L) (Node L) ℝ

lemma matrix_mem_spectrum_of_mulVec_eigenvector
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι ℝ) {μ : ℝ} {v : ι → ℝ}
    (hvne : v ≠ 0)
    (heig : A.mulVec v = fun i => μ * v i) :
    μ ∈ spectrum ℝ A := by
  have hlin : Matrix.toLin' A v = μ • v := by
    ext i
    rw [Matrix.toLin'_apply]
    simpa [Pi.smul_apply, smul_eq_mul] using congrFun heig i
  have hv : Module.End.HasEigenvector (Matrix.toLin' A) μ v := by
    rw [Module.End.hasEigenvector_iff]
    exact ⟨by simpa [Module.End.mem_eigenspace_iff] using hlin, hvne⟩
  have hval : Module.End.HasEigenvalue (Matrix.toLin' A) μ :=
    Module.End.hasEigenvalue_of_hasEigenvector hv
  have hspecLin : μ ∈ spectrum ℝ (Matrix.toLin' A) := hval.mem_spectrum
  simpa [Matrix.spectrum_toLin'] using hspecLin

namespace BoundaryLaplacianFamily

/-- Spectrum of an indexed finite Laplacian family at scale `L`. -/
noncomputable def spectralSet (F : BoundaryLaplacianFamily) (L : ℕ) : Set ℝ := by
  letI : Fintype (F.Node L) := F.nodeFintype L
  letI : DecidableEq (F.Node L) := F.nodeDecidableEq L
  exact _root_.spectrum ℝ (F.laplacian L)

theorem spectralSet_finite (F : BoundaryLaplacianFamily) (L : ℕ) :
    (F.spectralSet L).Finite := by
  classical
  unfold spectralSet
  letI : Fintype (F.Node L) := F.nodeFintype L
  letI : DecidableEq (F.Node L) := F.nodeDecidableEq L
  exact (F.laplacian L).finite_real_spectrum

noncomputable def laplacianMulVec (F : BoundaryLaplacianFamily) (L : ℕ)
    (v : F.Node L → ℝ) : F.Node L → ℝ := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  exact (F.laplacian L).mulVec v

noncomputable def nodeDot (F : BoundaryLaplacianFamily) (L : ℕ)
    (v w : F.Node L → ℝ) : ℝ := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  exact v ⬝ᵥ w

noncomputable def nodeNormSq (F : BoundaryLaplacianFamily) (L : ℕ)
    (v : F.Node L → ℝ) : ℝ :=
  F.nodeDot L v v

lemma nodeDot_laplacianMulVec_eq_eigenvalue_mul_nodeNormSq
    (F : BoundaryLaplacianFamily) (L : ℕ) {μ : ℝ} {v : F.Node L → ℝ}
    (heig : F.laplacianMulVec L v = fun i => μ * v i) :
    F.nodeDot L v (F.laplacianMulVec L v) = μ * F.nodeNormSq L v := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  rw [heig]
  simp only [nodeNormSq, nodeDot, dotProduct]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

lemma mem_spectralSet_of_eigenmode
    (F : BoundaryLaplacianFamily) (L : ℕ) {μ : ℝ} {v : F.Node L → ℝ}
    (hvne : v ≠ 0)
    (heig : F.laplacianMulVec L v = fun i => μ * v i) :
    μ ∈ F.spectralSet L := by
  classical
  unfold spectralSet
  unfold laplacianMulVec at heig
  letI : Fintype (F.Node L) := F.nodeFintype L
  letI : DecidableEq (F.Node L) := F.nodeDecidableEq L
  exact matrix_mem_spectrum_of_mulVec_eigenvector (F.laplacian L) hvne heig

end BoundaryLaplacianFamily

/--
Finite scalar stencil representation of one boundary-Laplacian matrix at scale
`L`.  It is deliberately local to one scale: the concrete Sigma overlap matrix
must still supply this representation.
-/
structure BoundaryScalarStencilAt (F : BoundaryLaplacianFamily) (L : ℕ)
    (Offset : Type*) [Fintype Offset] where
  center : ℝ
  weight : Offset → ℝ
  shift : Offset → F.Node L → F.Node L
  laplacian_apply :
    ∀ v i,
      F.laplacianMulVec L v i =
        center * v i - ∑ δ, weight δ * v (shift δ i)

namespace BoundaryScalarStencilAt

def eigenvalue {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt F L Offset) (phase : Offset → ℝ) : ℝ :=
  S.center - ∑ δ, S.weight δ * phase δ

theorem eigenmode_eq {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → ℝ}
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i) :
    F.laplacianMulVec L v = fun i => S.eigenvalue phase * v i := by
  ext i
  rw [S.laplacian_apply]
  have hsum :
      (∑ δ, S.weight δ * v (S.shift δ i)) =
        (∑ δ, S.weight δ * phase δ) * v i := by
    calc
      (∑ δ, S.weight δ * v (S.shift δ i)) =
          ∑ δ, S.weight δ * (phase δ * v i) := by
        refine Finset.sum_congr rfl ?_
        intro δ _
        rw [hshift δ i]
      _ = ∑ δ, (S.weight δ * phase δ) * v i := by
        refine Finset.sum_congr rfl ?_
        intro δ _
        ring
      _ = (∑ δ, S.weight δ * phase δ) * v i := by
        rw [Finset.sum_mul]
  rw [hsum]
  dsimp [eigenvalue]
  ring

theorem mem_spectralSet_of_shift_eigenmode
    {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i) :
    S.eigenvalue phase ∈ F.spectralSet L := by
  exact F.mem_spectralSet_of_eigenmode L hvne (S.eigenmode_eq hshift)

end BoundaryScalarStencilAt

/--
Finite row-dependent stencil representation of one boundary-Laplacian matrix at
scale `L`.  Unlike `BoundaryScalarStencilAt`, the weights and local symbol may
depend on the base node.  This is the exact interface for open-boundary and
non-translation-invariant matrices.
-/
structure BoundaryRowStencilAt (F : BoundaryLaplacianFamily) (L : ℕ)
    (Offset : Type*) [Fintype Offset] where
  center : F.Node L → ℝ
  weight : F.Node L → Offset → ℝ
  shift : Offset → F.Node L → F.Node L
  laplacian_apply :
    ∀ v i,
      F.laplacianMulVec L v i =
        center i * v i - ∑ δ, weight i δ * v (shift δ i)

namespace BoundaryRowStencilAt

noncomputable def rowAction {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset) (v : F.Node L → ℝ)
    (i : F.Node L) : ℝ :=
  S.center i * v i - ∑ δ, S.weight i δ * v (S.shift δ i)

lemma rowAction_eq_laplacianMulVec {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset) (v : F.Node L → ℝ)
    (i : F.Node L) :
    S.rowAction v i = F.laplacianMulVec L v i := by
  rw [rowAction, S.laplacian_apply]

noncomputable def rayleighNumerator {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset) (v : F.Node L → ℝ) : ℝ := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  exact ∑ i, v i * S.rowAction v i

lemma rayleighNumerator_eq_nodeDot_laplacianMulVec
    {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset) (v : F.Node L → ℝ) :
    S.rayleighNumerator v = F.nodeDot L v (F.laplacianMulVec L v) := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  simp [rayleighNumerator, BoundaryLaplacianFamily.nodeDot,
    rowAction_eq_laplacianMulVec, dotProduct]

def symbol {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset)
    (phase : Offset → F.Node L → ℝ) (i : F.Node L) : ℝ :=
  S.center i - ∑ δ, S.weight i δ * phase δ i

theorem eigenmode_eq_of_symbol_eq {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → F.Node L → ℝ} {μ : ℝ}
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ) :
    F.laplacianMulVec L v = fun i => μ * v i := by
  ext i
  rw [S.laplacian_apply]
  have hsum :
      (∑ δ, S.weight i δ * v (S.shift δ i)) =
        (∑ δ, S.weight i δ * phase δ i) * v i := by
    calc
      (∑ δ, S.weight i δ * v (S.shift δ i)) =
          ∑ δ, S.weight i δ * (phase δ i * v i) := by
        refine Finset.sum_congr rfl ?_
        intro δ _
        rw [hshift δ i]
      _ = ∑ δ, (S.weight i δ * phase δ i) * v i := by
        refine Finset.sum_congr rfl ?_
        intro δ _
        ring
      _ = (∑ δ, S.weight i δ * phase δ i) * v i := by
        rw [Finset.sum_mul]
  rw [hsum]
  rw [← hsymbol i]
  dsimp [symbol]
  ring

theorem mem_spectralSet_of_symbol_eigenmode
    {F : BoundaryLaplacianFamily} {L : ℕ}
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → F.Node L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ) :
    μ ∈ F.spectralSet L := by
  exact F.mem_spectralSet_of_eigenmode L hvne
    (S.eigenmode_eq_of_symbol_eq hshift hsymbol)

end BoundaryRowStencilAt

namespace BoundaryLaplacianFamily

/--
Exact finite row stencil attached to any matrix in a boundary Laplacian family.
The offsets are target nodes.  This representation is matrix-exact, but it does
not assert locality or translation invariance.
-/
noncomputable def fullRowStencil (F : BoundaryLaplacianFamily) (L : ℕ) :
    letI : Fintype (F.Node L) := F.nodeFintype L
    BoundaryRowStencilAt F L (F.Node L) := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  letI : DecidableEq (F.Node L) := F.nodeDecidableEq L
  refine
    { center := fun i => F.laplacian L i i
      weight := fun i j => if j = i then 0 else -F.laplacian L i j
      shift := fun j _ => j
      laplacian_apply := ?_ }
  intro v i
  change
    (∑ x, F.laplacian L i x * v x) =
      F.laplacian L i i * v i -
        ∑ x, (if x = i then 0 else -F.laplacian L i x) * v x
  simp only [ite_mul, zero_mul, neg_mul]
  have hsplit :=
    Finset.sum_erase_add (Finset.univ)
      (fun x => F.laplacian L i x * v x) (Finset.mem_univ i)
  rw [← hsplit]
  have hif :
      (∑ x, (if x = i then 0 else -(F.laplacian L i x * v x))) =
        -((Finset.univ.erase i).sum (fun x => F.laplacian L i x * v x)) := by
    calc
      (∑ x, (if x = i then 0 else -(F.laplacian L i x * v x))) =
          ∑ x,
            (if x ∈ Finset.univ.erase i then
              -(F.laplacian L i x * v x) else 0) := by
        refine Finset.sum_congr rfl ?_
        intro x _
        by_cases hx : x = i
        · subst hx
          simp
        · simp [hx, Finset.mem_erase]
      _ =
          (Finset.univ.erase i).sum
            (fun x => -(F.laplacian L i x * v x)) := by
        rw [Finset.sum_ite_mem]
        simp
      _ = -((Finset.univ.erase i).sum
            (fun x => F.laplacian L i x * v x)) := by
        rw [Finset.sum_neg_distrib]
  rw [hif]
  ring

lemma fullRowStencil_weight_eq_zero_of_laplacian_entry_zero
    (F : BoundaryLaplacianFamily) (L : ℕ) {i j : F.Node L}
    (hji : j ≠ i) (hA : F.laplacian L i j = 0) :
    letI : Fintype (F.Node L) := F.nodeFintype L
    (F.fullRowStencil L).weight i j = 0 := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  unfold fullRowStencil
  dsimp
  rw [if_neg hji, hA]
  norm_num

lemma fullRowStencil_weight_self
    (F : BoundaryLaplacianFamily) (L : ℕ) (i : F.Node L) :
    letI : Fintype (F.Node L) := F.nodeFintype L
    (F.fullRowStencil L).weight i i = 0 := by
  classical
  letI : Fintype (F.Node L) := F.nodeFintype L
  unfold fullRowStencil
  dsimp
  rw [if_pos rfl]

end BoundaryLaplacianFamily

/-- A boundary Laplacian family with the spectral properties needed pointwise in `L`. -/
structure SpectrallyClosedBoundaryLaplacianFamily where
  family : BoundaryLaplacianFamily
  spectrum_nonneg : ∀ L, 4 ≤ L → ∀ μ ∈ family.spectralSet L, 0 ≤ μ
  positive_spectral_gap :
    ∀ L, 4 ≤ L →
      ∃ γ : ℝ, 0 < γ ∧ ∀ μ ∈ family.spectralSet L, μ ≠ 0 → γ ≤ μ

namespace SpectrallyClosedBoundaryLaplacianFamily

theorem spectral_gap_exists (F : SpectrallyClosedBoundaryLaplacianFamily)
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧ ∀ μ ∈ F.family.spectralSet L, μ ≠ 0 → γ ≤ μ :=
  F.positive_spectral_gap L hL

theorem spectrum_nonnegative (F : SpectrallyClosedBoundaryLaplacianFamily)
    (L : ℕ) (hL : 4 ≤ L) :
    ∀ μ ∈ F.family.spectralSet L, 0 ≤ μ :=
  F.spectrum_nonneg L hL

end SpectrallyClosedBoundaryLaplacianFamily

/-- A sequence which realizes the first positive spectral value of a family. -/
structure BoundarySpectralValueRealization
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) where
  value_pos : ∀ L, 0 < lambda L
  value_mem : ∀ L, lambda L ∈ F.spectralSet L
  first_nonzero : ∀ L μ, μ ∈ F.spectralSet L → μ ≠ 0 → lambda L ≤ μ

/--
Eventual nonzero spectral content for a boundary family.  Together with
nonnegativity this is exactly the finite-dimensional input needed to select
the first positive spectral value from scale `L0` onward.
-/
structure BoundaryNonzeroSpectralValueExistsFrom
    (F : BoundaryLaplacianFamily) (L0 : ℕ) where
  L0_ge_four : 4 ≤ L0
  exists_nonzero : ∀ L, L0 ≤ L → ∃ μ : ℝ, μ ∈ F.spectralSet L ∧ μ ≠ 0

/-- Eventual realization of the first positive spectral value of a family. -/
structure BoundarySpectralValueRealizationFrom
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (L0 : ℕ) where
  value_pos : ∀ L, L0 ≤ L → 0 < lambda L
  value_mem : ∀ L, L0 ≤ L → lambda L ∈ F.spectralSet L
  first_nonzero :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 → lambda L ≤ μ

theorem firstPositiveSpectralValueFrom_exists
    (F : SpectrallyClosedBoundaryLaplacianFamily)
    {L0 : ℕ} (E : BoundaryNonzeroSpectralValueExistsFrom F.family L0)
    (L : ℕ) (hL : L0 ≤ L) :
    ∃ lam : ℝ, 0 < lam ∧ lam ∈ F.family.spectralSet L ∧
      ∀ μ ∈ F.family.spectralSet L, μ ≠ 0 → lam ≤ μ := by
  exact finite_first_positive_spectral_value
    (F.family.spectralSet_finite L)
    (F.spectrum_nonneg L (le_trans E.L0_ge_four hL))
    (E.exists_nonzero L hL)

/--
The first positive spectral value selected from a spectrally closed family,
once nonzero spectral content is known eventually.
-/
noncomputable def firstPositiveSpectralValueFrom
    (F : SpectrallyClosedBoundaryLaplacianFamily)
    {L0 : ℕ} (E : BoundaryNonzeroSpectralValueExistsFrom F.family L0) :
    ℕ → ℝ := fun L =>
  if hL : L0 ≤ L then
    Classical.choose (firstPositiveSpectralValueFrom_exists F E L hL)
  else 1

theorem firstPositiveSpectralValueFrom_spec
    (F : SpectrallyClosedBoundaryLaplacianFamily)
    {L0 : ℕ} (E : BoundaryNonzeroSpectralValueExistsFrom F.family L0)
    (L : ℕ) (hL : L0 ≤ L) :
    0 < firstPositiveSpectralValueFrom F E L ∧
      firstPositiveSpectralValueFrom F E L ∈ F.family.spectralSet L ∧
        ∀ μ ∈ F.family.spectralSet L, μ ≠ 0 →
          firstPositiveSpectralValueFrom F E L ≤ μ := by
  unfold firstPositiveSpectralValueFrom
  rw [dif_pos hL]
  exact Classical.choose_spec (firstPositiveSpectralValueFrom_exists F E L hL)

noncomputable def firstPositiveSpectralValueRealizationFrom
    (F : SpectrallyClosedBoundaryLaplacianFamily)
    {L0 : ℕ} (E : BoundaryNonzeroSpectralValueExistsFrom F.family L0) :
    BoundarySpectralValueRealizationFrom F.family
      (firstPositiveSpectralValueFrom F E) L0 where
  value_pos := by
    intro L hL
    exact (firstPositiveSpectralValueFrom_spec F E L hL).1
  value_mem := by
    intro L hL
    exact (firstPositiveSpectralValueFrom_spec F E L hL).2.1
  first_nonzero := by
    intro L hL μ hμ hμne
    exact (firstPositiveSpectralValueFrom_spec F E L hL).2.2 μ hμ hμne

namespace BoundarySpectralValueRealizationFrom

theorem le_of_spectral_nonzero {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L) {μ : ℝ}
    (hμmem : μ ∈ F.spectralSet L) (hμne : μ ≠ 0) :
    lambda L ≤ μ :=
  R.first_nonzero L hL μ hμmem hμne

theorem le_of_eigenmode {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L) {μ : ℝ} {v : F.Node L → ℝ}
    (hvne : v ≠ 0)
    (heig : F.laplacianMulVec L v = fun i => μ * v i)
    (hμne : μ ≠ 0) :
    lambda L ≤ μ := by
  exact R.le_of_spectral_nonzero hL
    (F.mem_spectralSet_of_eigenmode L hvne heig) hμne

theorem rescaled_value_upper_of_eigenmode
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L) {μ coefficient upperError : ℝ}
    {v : F.Node L → ℝ}
    (hvne : v ≠ 0)
    (heig : F.laplacianMulVec L v = fun i => μ * v i)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * lambda L ≤ coefficient + upperError := by
  have hfirst := R.le_of_eigenmode hL hvne heig hμne
  have hscale_nonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_left hfirst hscale_nonneg).trans hupper

theorem le_of_scalarStencilEigenmode
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0) :
    lambda L ≤ S.eigenvalue phase := by
  exact R.le_of_spectral_nonzero hL
    (S.mem_spectralSet_of_shift_eigenmode hvne hshift) hμne

theorem rescaled_value_upper_of_scalarStencilEigenmode
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → ℝ}
    {coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0)
    (hupper :
      (L : ℝ) ^ 2 * S.eigenvalue phase ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * lambda L ≤ coefficient + upperError := by
  have hfirst := R.le_of_scalarStencilEigenmode hL S hvne hshift hμne
  have hscale_nonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_left hfirst hscale_nonneg).trans hupper

theorem le_of_rowStencilEigenmode
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → F.Node L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0) :
    lambda L ≤ μ := by
  exact R.le_of_spectral_nonzero hL
    (S.mem_spectralSet_of_symbol_eigenmode hvne hshift hsymbol) hμne

theorem rescaled_value_upper_of_rowStencilEigenmode
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {L0 : ℕ}
    (R : BoundarySpectralValueRealizationFrom F lambda L0)
    {L : ℕ} (hL : L0 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt F L Offset)
    {v : F.Node L → ℝ} {phase : Offset → F.Node L → ℝ} {μ : ℝ}
    {coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * lambda L ≤ coefficient + upperError := by
  have hfirst := R.le_of_rowStencilEigenmode hL S hvne hshift hsymbol hμne
  have hscale_nonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  exact (mul_le_mul_of_nonneg_left hfirst hscale_nonneg).trans hupper

end BoundarySpectralValueRealizationFrom

/-- Full boundary spectral programme: realized boundary eigenvalue sequences plus limits. -/
structure BoundarySpectralLimitProgram where
  periodicFamily : BoundaryLaplacianFamily
  openFamily : BoundaryLaplacianFamily
  periodicLambda : ℕ → ℝ
  openLambda : ℕ → ℝ
  periodicRealization :
    BoundarySpectralValueRealization periodicFamily periodicLambda
  openRealization :
    BoundarySpectralValueRealization openFamily openLambda
  limit : BoundaryContinuumLimitCertificate periodicLambda openLambda

namespace BoundarySpectralLimitProgram

noncomputable def periodicScaling (P : BoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.periodicLambda :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling (P : BoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.openLambda :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK (P : BoundarySpectralLimitProgram) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0 (P : BoundarySpectralLimitProgram) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound (P : BoundarySpectralLimitProgram) :
    BoundaryDifferenceInverseSquareBound P.periodicLambda P.openLambda
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

theorem periodic_value_mem (P : BoundarySpectralLimitProgram) (L : ℕ) :
    P.periodicLambda L ∈ P.periodicFamily.spectralSet L :=
  P.periodicRealization.value_mem L

theorem open_value_mem (P : BoundarySpectralLimitProgram) (L : ℕ) :
    P.openLambda L ∈ P.openFamily.spectralSet L :=
  P.openRealization.value_mem L

end BoundarySpectralLimitProgram

/--
Asymptotic boundary spectral programme with first-positive eigenvalue
realization only from explicit scale thresholds onward.
-/
structure BoundarySpectralLimitProgramFrom where
  periodicFamily : BoundaryLaplacianFamily
  openFamily : BoundaryLaplacianFamily
  periodicLambda : ℕ → ℝ
  openLambda : ℕ → ℝ
  periodicL0 : ℕ
  openL0 : ℕ
  periodicRealization :
    BoundarySpectralValueRealizationFrom periodicFamily periodicLambda periodicL0
  openRealization :
    BoundarySpectralValueRealizationFrom openFamily openLambda openL0
  limit : BoundaryContinuumLimitCertificate periodicLambda openLambda

namespace BoundarySpectralLimitProgramFrom

noncomputable def periodicScaling (P : BoundarySpectralLimitProgramFrom) :
    InverseSquareSpectralScaling P.periodicLambda :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling (P : BoundarySpectralLimitProgramFrom) :
    InverseSquareSpectralScaling P.openLambda :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK (P : BoundarySpectralLimitProgramFrom) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0 (P : BoundarySpectralLimitProgramFrom) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound
    (P : BoundarySpectralLimitProgramFrom) :
    BoundaryDifferenceInverseSquareBound P.periodicLambda P.openLambda
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

theorem periodic_value_pos
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.periodicL0 ≤ L) :
    0 < P.periodicLambda L :=
  P.periodicRealization.value_pos L hL

theorem periodic_value_mem
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.periodicL0 ≤ L) :
    P.periodicLambda L ∈ P.periodicFamily.spectralSet L :=
  P.periodicRealization.value_mem L hL

theorem periodic_first_nonzero
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.periodicL0 ≤ L) :
    ∀ μ ∈ P.periodicFamily.spectralSet L,
      μ ≠ 0 → P.periodicLambda L ≤ μ :=
  P.periodicRealization.first_nonzero L hL

theorem open_value_pos
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.openL0 ≤ L) :
    0 < P.openLambda L :=
  P.openRealization.value_pos L hL

theorem open_value_mem
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.openL0 ≤ L) :
    P.openLambda L ∈ P.openFamily.spectralSet L :=
  P.openRealization.value_mem L hL

theorem open_first_nonzero
    (P : BoundarySpectralLimitProgramFrom) {L : ℕ} (hL : P.openL0 ≤ L) :
    ∀ μ ∈ P.openFamily.spectralSet L,
      μ ≠ 0 → P.openLambda L ≤ μ :=
  P.openRealization.first_nonzero L hL

end BoundarySpectralLimitProgramFrom

/--
Spectral bracketing certificate for a selected first positive boundary
eigenvalue.  A lower bound for every positive spectral value, together with one
positive spectral witness below the upper bracket, forces the selected first
positive eigenvalue into the same cubic window.
-/
structure BoundaryCubicSpectralBracketingCertificate
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (coefficient : ℝ) where
  L0 : ℕ
  L0_pos : 0 < L0
  realization : BoundarySpectralValueRealizationFrom F lambda L0
  lowerK : ℝ
  lowerK_nonneg : 0 ≤ lowerK
  upperK : ℝ
  upperK_nonneg : 0 ≤ upperK
  spectral_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      inverseSquareProfile coefficient L - lowerK / (L : ℝ) ^ 3 ≤ μ
  spectral_upper_witness :
    ∀ L, L0 ≤ L → ∃ μ : ℝ, μ ∈ F.spectralSet L ∧ μ ≠ 0 ∧
      μ ≤ inverseSquareProfile coefficient L + upperK / (L : ℝ) ^ 3

namespace BoundaryCubicSpectralBracketingCertificate

noncomputable def totalK {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ}
    {coefficient : ℝ}
    (C : BoundaryCubicSpectralBracketingCertificate F lambda coefficient) : ℝ :=
  C.lowerK + C.upperK

lemma totalK_nonneg {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ}
    {coefficient : ℝ}
    (C : BoundaryCubicSpectralBracketingCertificate F lambda coefficient) :
    0 ≤ C.totalK := by
  dsimp [totalK]
  exact add_nonneg C.lowerK_nonneg C.upperK_nonneg

theorem abs_eigenvalue_error_bound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryCubicSpectralBracketingCertificate F lambda coefficient) :
    ∀ L, C.L0 ≤ L →
      |lambda L - inverseSquareProfile coefficient L| ≤
        C.totalK / (L : ℝ) ^ 3 := by
  intro L hL
  have hLposNat : 0 < L := lt_of_lt_of_le C.L0_pos hL
  have hLrealpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hLposNat
  have hdennonneg : 0 ≤ (L : ℝ) ^ 3 := le_of_lt (pow_pos hLrealpos 3)
  have hlampos : 0 < lambda L := C.realization.value_pos L hL
  have hlamne : lambda L ≠ 0 := ne_of_gt hlampos
  have hlammem : lambda L ∈ F.spectralSet L := C.realization.value_mem L hL
  have hlower := C.spectral_lower L hL (lambda L) hlammem hlamne
  rcases C.spectral_upper_witness L hL with ⟨μ, hμmem, hμne, hμupper⟩
  have hfirst := C.realization.first_nonzero L hL μ hμmem hμne
  have hupper :
      lambda L ≤ inverseSquareProfile coefficient L + C.upperK / (L : ℝ) ^ 3 :=
    hfirst.trans hμupper
  have hlowerK_le_total : C.lowerK ≤ C.totalK := by
    dsimp [totalK]
    linarith [C.upperK_nonneg]
  have hupperK_le_total : C.upperK ≤ C.totalK := by
    dsimp [totalK]
    linarith [C.lowerK_nonneg]
  have hlowerDiv_le_total :
      C.lowerK / (L : ℝ) ^ 3 ≤ C.totalK / (L : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right hlowerK_le_total hdennonneg
  have hupperDiv_le_total :
      C.upperK / (L : ℝ) ^ 3 ≤ C.totalK / (L : ℝ) ^ 3 :=
    div_le_div_of_nonneg_right hupperK_le_total hdennonneg
  refine abs_le.mpr ?_
  constructor <;> linarith

end BoundaryCubicSpectralBracketingCertificate

/--
Open/periodic continuum bracketing package.  This is the source-facing form of
the remaining spectral asymptotics: prove spectral lower brackets and one
matching positive spectral witness for each boundary condition.
-/
structure BoundaryContinuumCubicSpectralBracketingCertificate
    (periodicFamily openFamily : BoundaryLaplacianFamily)
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic :
    BoundaryCubicSpectralBracketingCertificate periodicFamily periodicLambda
      (periodicSpectralContinuumCoefficient D_eff)
  openBoundary :
    BoundaryCubicSpectralBracketingCertificate openFamily openLambda
      (openSpectralContinuumCoefficient D_eff)

namespace BoundaryContinuumCubicSpectralBracketingCertificate

noncomputable def toCubicEigenvalueError
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodicK := C.periodic.totalK
  periodicK_nonneg := C.periodic.totalK_nonneg
  periodicL0 := C.periodic.L0
  periodicL0_pos := C.periodic.L0_pos
  openK := C.openBoundary.totalK
  openK_nonneg := C.openBoundary.totalK_nonneg
  openL0 := C.openBoundary.L0
  openL0_pos := C.openBoundary.L0_pos
  periodic_abs_eigenvalue_error_bound := by
    intro L hL
    simpa [periodicSpectralContinuumProfile] using
      C.periodic.abs_eigenvalue_error_bound L hL
  open_abs_eigenvalue_error_bound := by
    intro L hL
    simpa [openSpectralContinuumProfile] using
      C.openBoundary.abs_eigenvalue_error_bound L hL

noncomputable def toLimit
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumCubicSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toCubicEigenvalueError.toLimit

end BoundaryContinuumCubicSpectralBracketingCertificate

/--
Source-facing bracketing certificate for homogenised rescaled eigenvalues.
It matches compactness/homogenisation arguments: all positive spectral values
are eventually above the lower rescaled bracket, and one positive spectral
witness is below the upper rescaled bracket.
-/
structure BoundaryRescaledSpectralBracketingCertificate
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (coefficient : ℝ) where
  L0 : ℕ
  L0_pos : 0 < L0
  realization : BoundarySpectralValueRealizationFrom F lambda L0
  lowerError : ℕ → ℝ
  upperError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  spectral_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      coefficient - lowerError L ≤ (L : ℝ) ^ 2 * μ
  spectral_upper_witness :
    ∀ L, L0 ≤ L → ∃ μ : ℝ, μ ∈ F.spectralSet L ∧ μ ≠ 0 ∧
      (L : ℝ) ^ 2 * μ ≤ coefficient + upperError L

namespace BoundaryRescaledSpectralBracketingCertificate

noncomputable def errorBound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryRescaledSpectralBracketingCertificate F lambda coefficient) :
    ℕ → ℝ :=
  fun L => |C.lowerError L| + |C.upperError L|

lemma errorBound_tendsto_zero {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryRescaledSpectralBracketingCertificate F lambda coefficient) :
    Filter.Tendsto C.errorBound Filter.atTop (nhds 0) := by
  have hlower :
      Filter.Tendsto (fun L : ℕ => |C.lowerError L|)
        Filter.atTop (nhds 0) := by
    simpa using C.lowerError_tendsto_zero.abs
  have hupper :
      Filter.Tendsto (fun L : ℕ => |C.upperError L|)
        Filter.atTop (nhds 0) := by
    simpa using C.upperError_tendsto_zero.abs
  simpa [errorBound] using hlower.add hupper

theorem abs_rescaled_error_bound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryRescaledSpectralBracketingCertificate F lambda coefficient) :
    ∀ L, C.L0 ≤ L →
      |rescaledSpectralValue lambda L - coefficient| ≤ C.errorBound L := by
  intro L hL
  have hscale_nonneg : 0 ≤ (L : ℝ) ^ 2 := sq_nonneg _
  have hlampos : 0 < lambda L := C.realization.value_pos L hL
  have hlamne : lambda L ≠ 0 := ne_of_gt hlampos
  have hlammem : lambda L ∈ F.spectralSet L := C.realization.value_mem L hL
  have hlower := C.spectral_lower L hL (lambda L) hlammem hlamne
  rcases C.spectral_upper_witness L hL with ⟨μ, hμmem, hμne, hμupper⟩
  have hfirst := C.realization.first_nonzero L hL μ hμmem hμne
  have hfirst_scaled : (L : ℝ) ^ 2 * lambda L ≤ (L : ℝ) ^ 2 * μ :=
    mul_le_mul_of_nonneg_left hfirst hscale_nonneg
  have hupper_scaled :
      (L : ℝ) ^ 2 * lambda L ≤ coefficient + C.upperError L :=
    hfirst_scaled.trans hμupper
  have hleft_base :
      -C.lowerError L ≤ rescaledSpectralValue lambda L - coefficient := by
    unfold rescaledSpectralValue
    linarith
  have hright_base :
      rescaledSpectralValue lambda L - coefficient ≤ C.upperError L := by
    unfold rescaledSpectralValue
    linarith
  refine abs_le.mpr ?_
  constructor
  · have hlower_le_abs : C.lowerError L ≤ |C.lowerError L| := le_abs_self _
    have hupper_abs_nonneg : 0 ≤ |C.upperError L| := abs_nonneg _
    have hneg : -C.errorBound L ≤ -C.lowerError L := by
      dsimp [errorBound]
      linarith
    exact hneg.trans hleft_base
  · have hupper_le_abs : C.upperError L ≤ |C.upperError L| := le_abs_self _
    have hlower_abs_nonneg : 0 ≤ |C.lowerError L| := abs_nonneg _
    have hupper_total : C.upperError L ≤ C.errorBound L := by
      dsimp [errorBound]
      linarith
    exact hright_base.trans hupper_total

end BoundaryRescaledSpectralBracketingCertificate

/--
Constructive rescaled spectral bracketing.  The upper bracket is supplied by an
explicit positive spectral witness rather than an existential witness.
-/
structure BoundaryExplicitRescaledSpectralBracketingCertificate
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (coefficient : ℝ) where
  L0 : ℕ
  L0_pos : 0 < L0
  realization : BoundarySpectralValueRealizationFrom F lambda L0
  lowerError : ℕ → ℝ
  upperError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  witness : ℕ → ℝ
  witness_mem : ∀ L, L0 ≤ L → witness L ∈ F.spectralSet L
  witness_ne_zero : ∀ L, L0 ≤ L → witness L ≠ 0
  spectral_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      coefficient - lowerError L ≤ (L : ℝ) ^ 2 * μ
  witness_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * witness L ≤ coefficient + upperError L

namespace BoundaryExplicitRescaledSpectralBracketingCertificate

noncomputable def toRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryRescaledSpectralBracketingCertificate F lambda coefficient where
  L0 := C.L0
  L0_pos := C.L0_pos
  realization := C.realization
  lowerError := C.lowerError
  upperError := C.upperError
  lowerError_tendsto_zero := C.lowerError_tendsto_zero
  upperError_tendsto_zero := C.upperError_tendsto_zero
  spectral_lower := C.spectral_lower
  spectral_upper_witness := by
    intro L hL
    exact ⟨C.witness L, C.witness_mem L hL, C.witness_ne_zero L hL,
      C.witness_upper L hL⟩

noncomputable def errorBound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient) : ℕ → ℝ :=
  C.toRescaledSpectralBracketing.errorBound

lemma errorBound_tendsto_zero {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    Filter.Tendsto C.errorBound Filter.atTop (nhds 0) :=
  C.toRescaledSpectralBracketing.errorBound_tendsto_zero

theorem abs_rescaled_error_bound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    ∀ L, C.L0 ≤ L →
      |rescaledSpectralValue lambda L - coefficient| ≤ C.errorBound L :=
  C.toRescaledSpectralBracketing.abs_rescaled_error_bound

end BoundaryExplicitRescaledSpectralBracketingCertificate

/--
Open/periodic rescaled bracketing package.  This is the weakest source-facing
interface needed for the already formalised continuum-limit programme.
-/
structure BoundaryContinuumRescaledSpectralBracketingCertificate
    (periodicFamily openFamily : BoundaryLaplacianFamily)
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic :
    BoundaryRescaledSpectralBracketingCertificate periodicFamily periodicLambda
      (periodicSpectralContinuumCoefficient D_eff)
  openBoundary :
    BoundaryRescaledSpectralBracketingCertificate openFamily openLambda
      (openSpectralContinuumCoefficient D_eff)

namespace BoundaryContinuumRescaledSpectralBracketingCertificate

noncomputable def toAbsError
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodicErrorBound := C.periodic.errorBound
  openErrorBound := C.openBoundary.errorBound
  periodicErrorBound_tendsto_zero := C.periodic.errorBound_tendsto_zero
  openErrorBound_tendsto_zero := C.openBoundary.errorBound_tendsto_zero
  periodic_abs_error_bound := by
    filter_upwards [Filter.eventually_ge_atTop C.periodic.L0] with L hL
    simpa using C.periodic.abs_rescaled_error_bound L hL
  open_abs_error_bound := by
    filter_upwards [Filter.eventually_ge_atTop C.openBoundary.L0] with L hL
    simpa using C.openBoundary.abs_rescaled_error_bound L hL

noncomputable def toLimit
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toAbsError.toLimit

end BoundaryContinuumRescaledSpectralBracketingCertificate

/--
Open/periodic constructive rescaled bracketing package.  It records explicit
positive spectral witnesses for both boundary conditions.
-/
structure BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
    (periodicFamily openFamily : BoundaryLaplacianFamily)
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic :
    BoundaryExplicitRescaledSpectralBracketingCertificate
      periodicFamily periodicLambda (periodicSpectralContinuumCoefficient D_eff)
  openBoundary :
    BoundaryExplicitRescaledSpectralBracketingCertificate
      openFamily openLambda (openSpectralContinuumCoefficient D_eff)

namespace BoundaryContinuumExplicitRescaledSpectralBracketingCertificate

noncomputable def toRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic := C.periodic.toRescaledSpectralBracketing
  openBoundary := C.openBoundary.toRescaledSpectralBracketing

noncomputable def toAbsError
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda :=
  C.toRescaledSpectralBracketing.toAbsError

noncomputable def toLimit
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toRescaledSpectralBracketing.toLimit

end BoundaryContinuumExplicitRescaledSpectralBracketingCertificate

/--
Eigenmode-based rescaled spectral bracketing.  The upper witness is supplied
by an explicit eigenvalue/eigenmode pair for the boundary Laplacian family.
-/
structure BoundaryEigenmodeRescaledSpectralBracketingCertificate
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (coefficient : ℝ) where
  L0 : ℕ
  L0_pos : 0 < L0
  realization : BoundarySpectralValueRealizationFrom F lambda L0
  lowerError : ℕ → ℝ
  upperError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, F.Node L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_eq :
    ∀ L, L0 ≤ L →
      F.laplacianMulVec L (eigenmode L) =
        fun i => eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  spectral_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      coefficient - lowerError L ≤ (L : ℝ) ^ 2 * μ
  eigenvalue_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * eigenvalue L ≤ coefficient + upperError L

namespace BoundaryEigenmodeRescaledSpectralBracketingCertificate

noncomputable def toExplicitRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient where
  L0 := C.L0
  L0_pos := C.L0_pos
  realization := C.realization
  lowerError := C.lowerError
  upperError := C.upperError
  lowerError_tendsto_zero := C.lowerError_tendsto_zero
  upperError_tendsto_zero := C.upperError_tendsto_zero
  witness := C.eigenvalue
  witness_mem := by
    intro L hL
    exact F.mem_spectralSet_of_eigenmode L
      (C.eigenmode_ne_zero L hL) (C.eigenmode_eq L hL)
  witness_ne_zero := C.eigenvalue_ne_zero
  spectral_lower := C.spectral_lower
  witness_upper := C.eigenvalue_upper

noncomputable def toRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryRescaledSpectralBracketingCertificate F lambda coefficient :=
  C.toExplicitRescaledSpectralBracketing.toRescaledSpectralBracketing

noncomputable def errorBound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) : ℕ → ℝ :=
  C.toRescaledSpectralBracketing.errorBound

theorem abs_rescaled_error_bound {F : BoundaryLaplacianFamily}
    {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundaryEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    ∀ L, C.L0 ≤ L →
      |rescaledSpectralValue lambda L - coefficient| ≤ C.errorBound L :=
  C.toRescaledSpectralBracketing.abs_rescaled_error_bound

end BoundaryEigenmodeRescaledSpectralBracketingCertificate

/--
Lower half of the rescaled spectral bracketing argument at a fixed threshold:
every non-zero spectral value is bounded from below after `L^ 2` rescaling.
-/
structure BoundaryRescaledSpectralLowerCertificateAt
    (F : BoundaryLaplacianFamily) (coefficient : ℝ) (L0 : ℕ) where
  L0_pos : 0 < L0
  lowerError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  spectral_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      coefficient - lowerError L ≤ (L : ℝ) ^ 2 * μ

/--
Upper half of the rescaled spectral bracketing argument at a fixed threshold:
an explicit non-zero eigenmode supplies a positive spectral witness.
-/
structure BoundaryEigenmodeUpperWitnessCertificateAt
    (F : BoundaryLaplacianFamily) (coefficient : ℝ) (L0 : ℕ) where
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, F.Node L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_eq :
    ∀ L, L0 ≤ L →
      F.laplacianMulVec L (eigenmode L) =
        fun i => eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  eigenvalue_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * eigenvalue L ≤ coefficient + upperError L

namespace BoundaryEigenmodeUpperWitnessCertificateAt

theorem eigenvalue_mem {F : BoundaryLaplacianFamily} {coefficient : ℝ}
    {L0 : ℕ} (C : BoundaryEigenmodeUpperWitnessCertificateAt F coefficient L0) :
    ∀ L, L0 ≤ L → C.eigenvalue L ∈ F.spectralSet L := by
  intro L hL
  exact F.mem_spectralSet_of_eigenmode L
    (C.eigenmode_ne_zero L hL) (C.eigenmode_eq L hL)

end BoundaryEigenmodeUpperWitnessCertificateAt

/--
Rayleigh-form upper witness for one boundary family.  The analytic obligation is
the normalized Rayleigh upper bound; the conversion below turns it into the
existing eigenmode upper witness interface.
-/
structure BoundaryRayleighUpperWitnessCertificateAt
    (F : BoundaryLaplacianFamily) (coefficient : ℝ) (L0 : ℕ) where
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, F.Node L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_norm_one :
    ∀ L, L0 ≤ L → F.nodeNormSq L (eigenmode L) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L →
      F.laplacianMulVec L (eigenmode L) =
        fun i => eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  rayleigh_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * F.nodeDot L (eigenmode L)
        (F.laplacianMulVec L (eigenmode L)) ≤ coefficient + upperError L

namespace BoundaryRayleighUpperWitnessCertificateAt

noncomputable def toEigenmodeUpperWitness
    {F : BoundaryLaplacianFamily} {coefficient : ℝ} {L0 : ℕ}
    (C : BoundaryRayleighUpperWitnessCertificateAt F coefficient L0) :
    BoundaryEigenmodeUpperWitnessCertificateAt F coefficient L0 where
  L0_pos := C.L0_pos
  upperError := C.upperError
  upperError_tendsto_zero := C.upperError_tendsto_zero
  eigenvalue := C.eigenvalue
  eigenmode := C.eigenmode
  eigenmode_ne_zero := C.eigenmode_ne_zero
  eigenmode_eq := C.eigenmode_eq
  eigenvalue_ne_zero := C.eigenvalue_ne_zero
  eigenvalue_upper := by
    intro L hL
    have hdot :=
      BoundaryLaplacianFamily.nodeDot_laplacianMulVec_eq_eigenvalue_mul_nodeNormSq
        F L (μ := C.eigenvalue L) (v := C.eigenmode L)
        (C.eigenmode_eq L hL)
    have hdot' :
        F.nodeDot L (C.eigenmode L)
            (F.laplacianMulVec L (C.eigenmode L)) = C.eigenvalue L := by
      simpa [C.eigenmode_norm_one L hL] using hdot
    simpa [hdot'] using C.rayleigh_upper L hL

end BoundaryRayleighUpperWitnessCertificateAt

/--
Rayleigh-form lower certificate for one boundary family.  For every non-zero
spectral value it records a normalized eigenmode and a Rayleigh lower bound;
the conversion below gives the existing rescaled spectral lower interface.
-/
structure BoundaryRayleighSpectralLowerCertificateAt
    (F : BoundaryLaplacianFamily) (coefficient : ℝ) (L0 : ℕ) where
  L0_pos : 0 < L0
  lowerError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  eigenmode : ∀ L, ℝ → F.Node L → ℝ
  eigenmode_norm_one :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      F.nodeNormSq L (eigenmode L μ) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      F.laplacianMulVec L (eigenmode L μ) =
        fun i => μ * eigenmode L μ i
  rayleigh_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ F.spectralSet L, μ ≠ 0 →
      coefficient - lowerError L ≤
        (L : ℝ) ^ 2 * F.nodeDot L (eigenmode L μ)
          (F.laplacianMulVec L (eigenmode L μ))

namespace BoundaryRayleighSpectralLowerCertificateAt

noncomputable def toRescaledSpectralLower
    {F : BoundaryLaplacianFamily} {coefficient : ℝ} {L0 : ℕ}
    (C : BoundaryRayleighSpectralLowerCertificateAt F coefficient L0) :
    BoundaryRescaledSpectralLowerCertificateAt F coefficient L0 where
  L0_pos := C.L0_pos
  lowerError := C.lowerError
  lowerError_tendsto_zero := C.lowerError_tendsto_zero
  spectral_lower := by
    intro L hL μ hμmem hμne
    have hdot :=
      BoundaryLaplacianFamily.nodeDot_laplacianMulVec_eq_eigenvalue_mul_nodeNormSq
        F L (μ := μ) (v := C.eigenmode L μ)
        (C.eigenmode_eq L hL μ hμmem hμne)
    have hdot' :
        F.nodeDot L (C.eigenmode L μ)
            (F.laplacianMulVec L (C.eigenmode L μ)) = μ := by
      simpa [C.eigenmode_norm_one L hL μ hμmem hμne] using hdot
    simpa [hdot'] using C.rayleigh_lower L hL μ hμmem hμne

end BoundaryRayleighSpectralLowerCertificateAt

/--
Split eigenmode bracketing certificate.  The lower spectral coercivity and the
upper explicit eigenmode witness are independent obligations sharing the same
large-scale threshold.
-/
structure BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
    (F : BoundaryLaplacianFamily) (lambda : ℕ → ℝ) (coefficient : ℝ) where
  L0 : ℕ
  realization : BoundarySpectralValueRealizationFrom F lambda L0
  lower : BoundaryRescaledSpectralLowerCertificateAt F coefficient L0
  upper : BoundaryEigenmodeUpperWitnessCertificateAt F coefficient L0

namespace BoundarySplitEigenmodeRescaledSpectralBracketingCertificate

noncomputable def toEigenmodeRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient where
  L0 := C.L0
  L0_pos := C.lower.L0_pos
  realization := C.realization
  lowerError := C.lower.lowerError
  upperError := C.upper.upperError
  lowerError_tendsto_zero := C.lower.lowerError_tendsto_zero
  upperError_tendsto_zero := C.upper.upperError_tendsto_zero
  eigenvalue := C.upper.eigenvalue
  eigenmode := C.upper.eigenmode
  eigenmode_ne_zero := C.upper.eigenmode_ne_zero
  eigenmode_eq := C.upper.eigenmode_eq
  eigenvalue_ne_zero := C.upper.eigenvalue_ne_zero
  spectral_lower := C.lower.spectral_lower
  eigenvalue_upper := C.upper.eigenvalue_upper

noncomputable def toExplicitRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryExplicitRescaledSpectralBracketingCertificate
      F lambda coefficient :=
  C.toEigenmodeRescaledSpectralBracketing.toExplicitRescaledSpectralBracketing

noncomputable def toRescaledSpectralBracketing
    {F : BoundaryLaplacianFamily} {lambda : ℕ → ℝ} {coefficient : ℝ}
    (C : BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      F lambda coefficient) :
    BoundaryRescaledSpectralBracketingCertificate F lambda coefficient :=
  C.toEigenmodeRescaledSpectralBracketing.toRescaledSpectralBracketing

end BoundarySplitEigenmodeRescaledSpectralBracketingCertificate

/--
Open/periodic eigenmode-based rescaled bracketing package.  This is the
interface for explicit Fourier/sine-mode spectral witnesses.
-/
structure BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
    (periodicFamily openFamily : BoundaryLaplacianFamily)
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic :
    BoundaryEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily periodicLambda (periodicSpectralContinuumCoefficient D_eff)
  openBoundary :
    BoundaryEigenmodeRescaledSpectralBracketingCertificate
      openFamily openLambda (openSpectralContinuumCoefficient D_eff)

namespace BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate

noncomputable def toExplicitRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic := C.periodic.toExplicitRescaledSpectralBracketing
  openBoundary := C.openBoundary.toExplicitRescaledSpectralBracketing

noncomputable def toRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda :=
  C.toExplicitRescaledSpectralBracketing.toRescaledSpectralBracketing

noncomputable def toAbsError
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda :=
  C.toRescaledSpectralBracketing.toAbsError

noncomputable def toLimit
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toRescaledSpectralBracketing.toLimit

end BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate

/--
Open/periodic split eigenmode bracketing package.  This isolates the remaining
continuum-limit work into lower coercivity and explicit-mode upper witnesses
for each boundary condition.
-/
structure BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
    (periodicFamily openFamily : BoundaryLaplacianFamily)
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodic :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily periodicLambda (periodicSpectralContinuumCoefficient D_eff)
  openBoundary :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      openFamily openLambda (openSpectralContinuumCoefficient D_eff)

namespace BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate

noncomputable def toEigenmodeRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic := C.periodic.toEigenmodeRescaledSpectralBracketing
  openBoundary := C.openBoundary.toEigenmodeRescaledSpectralBracketing

noncomputable def toExplicitRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda :=
  C.toEigenmodeRescaledSpectralBracketing.toExplicitRescaledSpectralBracketing

noncomputable def toRescaledSpectralBracketing
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda :=
  C.toEigenmodeRescaledSpectralBracketing.toRescaledSpectralBracketing

noncomputable def toAbsError
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumAbsErrorBoundCertificate periodicLambda openLambda :=
  C.toEigenmodeRescaledSpectralBracketing.toAbsError

noncomputable def toLimit
    {periodicFamily openFamily : BoundaryLaplacianFamily}
    {periodicLambda openLambda : ℕ → ℝ}
    (C : BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      periodicFamily openFamily periodicLambda openLambda) :
    BoundaryContinuumLimitCertificate periodicLambda openLambda :=
  C.toEigenmodeRescaledSpectralBracketing.toLimit

end BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate

theorem randomWalkLaplacian_spectralFrame_heatFlow_decay
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    {κ : Type*} [Fintype κ]
    (F : MatrixSpectralFrame (randomWalkLaplacian S) κ)
    (hspec : ∀ k, F.freq k ∈ spectrum ℝ (randomWalkLaplacian S)) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ n, ReducedModalCoefficients F.freq (F.coords x) →
        γ * modalEnergy (F.coords x) ≤ modalDirichletEnergy F.freq (F.coords x) ∧
          ∀ t : ℝ, 0 ≤ t →
            ‖F.heatFlow t x‖ ^ 2 ≤ Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  rcases randomWalkLaplacian_positive_spectral_gap S hsymm hnonneg hpos with
    ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro x hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (F.freq k) (hspec k) hne)
  · intro t ht
    exact F.heatFlow_energy_decay hreduced
      (fun k hne => hgap (F.freq k) (hspec k) hne) ht

noncomputable def similaritySymmetrizedLaplacianSpectralFrame
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j) :
    MatrixSpectralFrame (similaritySymmetrizedLaplacian S) n :=
  hermitianSpectralFrame
    (similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg).isHermitian

theorem similaritySymmetrizedLaplacian_canonicalHeatFlow_decay
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ n,
        ReducedModalCoefficients
          (similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).freq
          ((similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).coords x) →
          γ * modalEnergy
              ((similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).coords x) ≤
              modalDirichletEnergy
                (similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).freq
                ((similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖(similaritySymmetrizedLaplacianSpectralFrame S hsymm hnonneg).heatFlow
                t x‖ ^ 2 ≤
                Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  exact posSemidef_hermitianSpectralFrame_heatFlow_decay
    (similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg)

/--
Source-grounded core of the Appendix-VI block-Laplacian theorem:
the similarity-symmetrized Laplacian is positive semidefinite, and the random-walk
Laplacian has exactly the constant kernel on a connected support graph.
-/
theorem blockLaplacian_core
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hdeg : ∀ i, blockDegree S i ≠ 0)
    (hconn : (supportGraph S hsymm).Connected) :
    (similaritySymmetrizedLaplacian S).PosSemidef ∧
      ∀ x : n → ℝ,
        (randomWalkLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  exact ⟨similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg,
    fun x => randomWalkLaplacian_mulVec_eq_zero_iff_exists_const
      S hsymm hnonneg hdeg hconn x⟩

/--
Source-grounded Appendix-VI block-Laplacian theorem in the concrete
`D^{1/2} A D^{-1/2}` form.
-/
theorem blockLaplacian
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    (hconn : (supportGraph S hsymm).Connected) :
    (similaritySymmetrizedLaplacian S).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), 0 ≤ μ) ∧
        ∀ x : n → ℝ,
          (randomWalkLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  have hdeg : ∀ i, blockDegree S i ≠ 0 := fun i => ne_of_gt (hpos i)
  exact ⟨similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg,
    randomWalkLaplacian_spectrum_nonneg S hsymm hnonneg hpos,
    fun x => randomWalkLaplacian_mulVec_eq_zero_iff_exists_const
      S hsymm hnonneg hdeg hconn x⟩

theorem blockLaplacian_positive_spectral_gap
    (S : Matrix n n ℝ) (hsymm : S.IsSymm) (hnonneg : ∀ i j, 0 ≤ S i j)
    (hpos : ∀ i, 0 < blockDegree S i)
    (hconn : (supportGraph S hsymm).Connected) :
    (similaritySymmetrizedLaplacian S).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), 0 ≤ μ) ∧
        (∃ γ : ℝ, 0 < γ ∧
          ∀ μ ∈ spectrum ℝ (randomWalkLaplacian S), μ ≠ 0 → γ ≤ μ) ∧
          ∀ x : n → ℝ,
            (randomWalkLaplacian S).mulVec x = 0 ↔ ∃ c : ℝ, x = fun _ => c := by
  have hdeg : ∀ i, blockDegree S i ≠ 0 := fun i => ne_of_gt (hpos i)
  exact ⟨similaritySymmetrizedLaplacian_posSemidef S hsymm hnonneg,
    randomWalkLaplacian_spectrum_nonneg S hsymm hnonneg hpos,
    randomWalkLaplacian_positive_spectral_gap S hsymm hnonneg hpos,
    fun x => randomWalkLaplacian_mulVec_eq_zero_iff_exists_const
      S hsymm hnonneg hdeg hconn x⟩

def BlockRowsNonnegative {ι ε : Type*} (M : Matrix ι ε ℝ) : Prop :=
  ∀ i e, 0 ≤ M i e

def BlockRowsStochastic {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ) : Prop :=
  ∀ i, ∑ e, M i e = 1

/-- Rectangular block-overlap weights `S = M Mᵀ`. -/
def coarseOverlapMatrix {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ) :
    Matrix ι ι ℝ :=
  M * Mᵀ

lemma coarseOverlapMatrix_apply
    {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ) (i j : ι) :
    coarseOverlapMatrix M i j = ∑ e, M i e * M j e := by
  simp [coarseOverlapMatrix, Matrix.mul_apply]

lemma blockDegree_coarseOverlapMatrix_apply
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (M : Matrix ι ε ℝ) (i : ι) :
    blockDegree (coarseOverlapMatrix M) i =
      ∑ e, M i e * ∑ j, M j e := by
  classical
  unfold blockDegree
  simp only [coarseOverlapMatrix_apply, Finset.mul_sum]
  rw [Finset.sum_comm]

lemma coarseOverlapMatrix_isSymm
    {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ) :
    (coarseOverlapMatrix M).IsSymm := by
  rw [Matrix.IsSymm]
  ext i j
  simp [coarseOverlapMatrix, Matrix.mul_apply, mul_comm]

lemma coarseOverlapMatrix_nonneg
    {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) :
    ∀ i j, 0 ≤ coarseOverlapMatrix M i j := by
  intro i j
  rw [coarseOverlapMatrix_apply]
  exact Finset.sum_nonneg fun e _ => mul_nonneg (hnonneg i e) (hnonneg j e)

lemma coarseOverlapMatrix_diag_pos
    {ι ε : Type*} [Fintype ε] (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) (hstoch : BlockRowsStochastic M) :
    ∀ i, 0 < coarseOverlapMatrix M i i := by
  classical
  intro i
  have hexists : ∃ e, M i e ≠ 0 := by
    by_contra hnone
    have hzero : ∀ e, M i e = 0 := by
      intro e
      by_contra hne
      exact hnone ⟨e, hne⟩
    have hsum_zero : ∑ e, M i e = 0 := by
      simp [hzero]
    have hone_zero : (1 : ℝ) = 0 := by
      rw [← hstoch i, hsum_zero]
    norm_num at hone_zero
  rcases hexists with ⟨e0, he0⟩
  rw [coarseOverlapMatrix_apply]
  refine Finset.sum_pos' (fun e _ => mul_nonneg (hnonneg i e) (hnonneg i e)) ?_
  exact ⟨e0, Finset.mem_univ e0, mul_self_pos.mpr he0⟩

lemma coarseOverlapMatrix_degree_pos
    {ι ε : Type*} [Fintype ι] [Fintype ε]
    (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) (hstoch : BlockRowsStochastic M) :
    ∀ i, 0 < blockDegree (coarseOverlapMatrix M) i := by
  classical
  intro i
  have hdiag : 0 < coarseOverlapMatrix M i i :=
    coarseOverlapMatrix_diag_pos M hnonneg hstoch i
  have hle : coarseOverlapMatrix M i i ≤ ∑ j, coarseOverlapMatrix M i j := by
    exact Finset.single_le_sum
      (fun j _ => coarseOverlapMatrix_nonneg M hnonneg i j) (Finset.mem_univ i)
  exact hdiag.trans_le hle

/--
Algebraic upstream form of the Appendix-VI construction:
a nonnegative row-stochastic rectangular block matrix produces the square overlap matrix
`S = M Mᵀ`, and the closed block-Laplacian theorem applies to this `S`.
-/
theorem blockAveragingMatrix_blockLaplacian
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) (hstoch : BlockRowsStochastic M)
    (hconn :
      (supportGraph (coarseOverlapMatrix M)
        (coarseOverlapMatrix_isSymm M)).Connected) :
    (similaritySymmetrizedLaplacian (coarseOverlapMatrix M)).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ (randomWalkLaplacian (coarseOverlapMatrix M)), 0 ≤ μ) ∧
        ∀ x : ι → ℝ,
          (randomWalkLaplacian (coarseOverlapMatrix M)).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact blockLaplacian (coarseOverlapMatrix M) (coarseOverlapMatrix_isSymm M)
    (coarseOverlapMatrix_nonneg M hnonneg)
    (coarseOverlapMatrix_degree_pos M hnonneg hstoch) hconn

theorem blockAveragingMatrix_exists_nonzero_spectral_value
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [Nontrivial ι]
    (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) (hstoch : BlockRowsStochastic M)
    (hconn :
      (supportGraph (coarseOverlapMatrix M)
        (coarseOverlapMatrix_isSymm M)).Connected) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ (randomWalkLaplacian (coarseOverlapMatrix M)) ∧
      μ ≠ 0 := by
  have hblock :=
    blockAveragingMatrix_blockLaplacian M hnonneg hstoch hconn
  exact randomWalkLaplacian_exists_nonzero_spectral_value_of_constant_kernel
    (coarseOverlapMatrix M) (coarseOverlapMatrix_isSymm M)
    (coarseOverlapMatrix_nonneg M hnonneg)
    (coarseOverlapMatrix_degree_pos M hnonneg hstoch) hblock.2.2

theorem blockAveragingMatrix_positive_spectral_gap
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε]
    (M : Matrix ι ε ℝ)
    (hnonneg : BlockRowsNonnegative M) (hstoch : BlockRowsStochastic M) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ (randomWalkLaplacian (coarseOverlapMatrix M)),
        μ ≠ 0 → γ ≤ μ := by
  exact randomWalkLaplacian_positive_spectral_gap
    (coarseOverlapMatrix M) (coarseOverlapMatrix_isSymm M)
    (coarseOverlapMatrix_nonneg M hnonneg)
    (coarseOverlapMatrix_degree_pos M hnonneg hstoch)

/--
Concrete block-averaging matrix from finite supports `E_i`:
`M i e = 1 / |E_i|` on the support and `0` off it.
-/
noncomputable def blockAveragingMatrixFromSupports
    {ι ε : Type*} [DecidableEq ε] (E : ι → Finset ε) : Matrix ι ε ℝ :=
  fun i e => if e ∈ E i then ((E i).card : ℝ)⁻¹ else 0

lemma blockAveragingMatrixFromSupports_nonnegative
    {ι ε : Type*} [DecidableEq ε] (E : ι → Finset ε) :
    BlockRowsNonnegative (blockAveragingMatrixFromSupports E) := by
  intro i e
  by_cases he : e ∈ E i
  · dsimp [blockAveragingMatrixFromSupports]
    rw [if_pos he]
    exact inv_nonneg.mpr (Nat.cast_nonneg _)
  · simp [blockAveragingMatrixFromSupports, he]

lemma blockAveragingMatrixFromSupports_rowStochastic
    {ι ε : Type*} [Fintype ε] [DecidableEq ε] (E : ι → Finset ε)
    (hnonempty : ∀ i, (E i).Nonempty) :
    BlockRowsStochastic (blockAveragingMatrixFromSupports E) := by
  classical
  intro i
  have hcard : ((E i).card : ℝ) ≠ 0 := by
    exact_mod_cast (hnonempty i).card_ne_zero
  calc
    ∑ e, blockAveragingMatrixFromSupports E i e =
        ∑ e, if e ∈ E i then ((E i).card : ℝ)⁻¹ else 0 := by
      rfl
    _ = (E i).sum (fun _ => ((E i).card : ℝ)⁻¹) := by
      rw [Finset.sum_ite_mem_eq]
    _ = ((E i).card : ℝ) * ((E i).card : ℝ)⁻¹ := by
      simp [Finset.sum_const, nsmul_eq_mul]
    _ = 1 := by
      exact mul_inv_cancel₀ hcard

/-- The source-level block-star overlap graph: two blocks are adjacent when
their finite fine-edge supports overlap. -/
def blockSupportOverlapGraph {ι ε : Type*} [DecidableEq ε]
    (E : ι → Finset ε) : SimpleGraph ι where
  Adj i j := i ≠ j ∧ (E i ∩ E j).Nonempty
  symm := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    rcases hij.2 with ⟨e, he⟩
    exact ⟨e, by simpa [Finset.mem_inter, and_comm] using he⟩

lemma blockSupportOverlapGraph_le_supportGraph
    {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) :
    blockSupportOverlapGraph E ≤
      supportGraph (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
        (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E)) := by
  classical
  intro i j hij
  refine ⟨hij.1, ?_⟩
  rcases hij.2 with ⟨e0, he0⟩
  have hi : e0 ∈ E i := (Finset.mem_inter.mp he0).1
  have hj : e0 ∈ E j := (Finset.mem_inter.mp he0).2
  rw [coarseOverlapMatrix_apply]
  refine Finset.sum_pos' ?_ ?_
  · intro e _
    exact mul_nonneg
      (blockAveragingMatrixFromSupports_nonnegative E i e)
      (blockAveragingMatrixFromSupports_nonnegative E j e)
  · refine ⟨e0, Finset.mem_univ e0, ?_⟩
    have hMi : 0 < blockAveragingMatrixFromSupports E i e0 := by
      dsimp [blockAveragingMatrixFromSupports]
      rw [if_pos hi]
      exact inv_pos.mpr (by exact_mod_cast (Finset.card_pos.mpr ⟨e0, hi⟩))
    have hMj : 0 < blockAveragingMatrixFromSupports E j e0 := by
      dsimp [blockAveragingMatrixFromSupports]
      rw [if_pos hj]
      exact inv_pos.mpr (by exact_mod_cast (Finset.card_pos.mpr ⟨e0, hj⟩))
    exact mul_pos hMi hMj

lemma blockSupportOverlapGraph_connected_to_supportGraph_connected
    {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε)
    (hconn : (blockSupportOverlapGraph E).Connected) :
    (supportGraph
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
      (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E))).Connected :=
  hconn.mono (blockSupportOverlapGraph_le_supportGraph E)

lemma coarseOverlapMatrix_fromSupports_apply_eq_inter_card
    {ι ε : Type*} [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) (i j : ι) :
    coarseOverlapMatrix (blockAveragingMatrixFromSupports E) i j =
      ((E i ∩ E j).card : ℝ) *
        ((E i).card : ℝ)⁻¹ * ((E j).card : ℝ)⁻¹ := by
  classical
  rw [coarseOverlapMatrix_apply]
  calc
    ∑ e,
        blockAveragingMatrixFromSupports E i e *
          blockAveragingMatrixFromSupports E j e =
        ∑ e,
          if e ∈ E i ∩ E j then
            ((E i).card : ℝ)⁻¹ * ((E j).card : ℝ)⁻¹
          else 0 := by
      refine Finset.sum_congr rfl ?_
      intro e _
      by_cases hi : e ∈ E i <;> by_cases hj : e ∈ E j <;>
        simp [blockAveragingMatrixFromSupports, hi, hj, Finset.mem_inter]
    _ = (E i ∩ E j).sum
        (fun _ => ((E i).card : ℝ)⁻¹ * ((E j).card : ℝ)⁻¹) := by
      rw [Finset.sum_ite_mem_eq]
    _ = ((E i ∩ E j).card : ℝ) *
        ((E i).card : ℝ)⁻¹ * ((E j).card : ℝ)⁻¹ := by
      simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]

lemma coarseOverlapMatrix_fromSupports_eq_zero_of_disjoint
    {ι ε : Type*} [Fintype ε] [DecidableEq ε] (E : ι → Finset ε)
    {i j : ι} (hdisj : Disjoint (E i) (E j)) :
    coarseOverlapMatrix (blockAveragingMatrixFromSupports E) i j = 0 := by
  rw [coarseOverlapMatrix_apply]
  refine Finset.sum_eq_zero ?_
  intro e _
  by_cases hi : e ∈ E i
  · have hnotj : e ∉ E j := by
      intro hj
      exact (Finset.disjoint_left.mp hdisj) hi hj
    simp [blockAveragingMatrixFromSupports, hi, hnotj]
  · simp [blockAveragingMatrixFromSupports, hi]

/-- Local-support form of Appendix-VI locality: a distantness relation whose
distant blocks have disjoint supports forces zero coarse overlap. -/
def BlockSupportsLocal {ι ε : Type*} (E : ι → Finset ε) (Distant : ι → ι → Prop) :
    Prop :=
  ∀ {i j}, Distant i j → Disjoint (E i) (E j)

lemma blockSupportsLocal_zero
    {ι ε : Type*} [Fintype ε] [DecidableEq ε] (E : ι → Finset ε)
    (Distant : ι → ι → Prop) (hlocal : BlockSupportsLocal E Distant)
    {i j : ι} (hdistant : Distant i j) :
    coarseOverlapMatrix (blockAveragingMatrixFromSupports E) i j = 0 :=
  coarseOverlapMatrix_fromSupports_eq_zero_of_disjoint E (hlocal hdistant)

/--
Planck/no-zero clock data: every primitive support carrier has a positive
integer multiple of a positive Planck unit as its elementary time readout.
This is the Lean-facing form of sigma.P needed upstream of Appendix VI.
-/
structure SigmaPlanckNoZeroClock (ε : Type*) where
  planckUnit : ℝ
  planckUnit_pos : 0 < planckUnit
  primitiveTime : ε → ℝ
  primitiveTime_multiple :
    ∀ e, ∃ N : ℕ, 0 < N ∧ primitiveTime e = (N : ℝ) * planckUnit

namespace SigmaPlanckNoZeroClock

lemma primitiveTime_pos {ε : Type*} (C : SigmaPlanckNoZeroClock ε) (e : ε) :
    0 < C.primitiveTime e := by
  rcases C.primitiveTime_multiple e with ⟨N, hNpos, htime⟩
  rw [htime]
  exact mul_pos (Nat.cast_pos.mpr hNpos) C.planckUnit_pos

lemma primitiveTime_ne_zero {ε : Type*} (C : SigmaPlanckNoZeroClock ε) (e : ε) :
    C.primitiveTime e ≠ 0 :=
  ne_of_gt (C.primitiveTime_pos e)

end SigmaPlanckNoZeroClock

/-- Minimal source-level sigma block-star covering data used in Appendix VI:
the coarse star-adjacency graph is connected and adjacent stars share a fine edge. -/
structure SigmaBlockStarCovering (ι ε : Type*) [DecidableEq ε] where
  coarseGraph : SimpleGraph ι
  fineEdgeSupport : ι → Finset ε
  support_nonempty : ∀ i, (fineEdgeSupport i).Nonempty
  coarse_connected : coarseGraph.Connected
  adjacent_share_fine_edge :
    ∀ {i j}, coarseGraph.Adj i j → (fineEdgeSupport i ∩ fineEdgeSupport j).Nonempty

namespace SigmaBlockStarCovering

lemma coarseGraph_le_overlapGraph
    {ι ε : Type*} [DecidableEq ε] (C : SigmaBlockStarCovering ι ε) :
    C.coarseGraph ≤ blockSupportOverlapGraph C.fineEdgeSupport := by
  intro i j hij
  exact ⟨hij.ne, C.adjacent_share_fine_edge hij⟩

lemma overlapGraph_connected
    {ι ε : Type*} [DecidableEq ε] (C : SigmaBlockStarCovering ι ε) :
    (blockSupportOverlapGraph C.fineEdgeSupport).Connected :=
  C.coarse_connected.mono (C.coarseGraph_le_overlapGraph)

end SigmaBlockStarCovering

/--
Source-level Appendix VI bridge: Planck-positive primitive carriers together
with connected finite block-star overlap data generate the Lean start object
`SigmaBlockStarCovering`.
-/
structure SigmaPlanckBlockStarSource (ι ε : Type*) [DecidableEq ε] where
  clock : SigmaPlanckNoZeroClock ε
  coarseGraph : SimpleGraph ι
  fineEdgeSupport : ι → Finset ε
  support_planck_nonempty :
    ∀ i, ∃ e ∈ fineEdgeSupport i, 0 < clock.primitiveTime e
  coarse_connected : coarseGraph.Connected
  adjacent_share_fine_edge :
    ∀ {i j}, coarseGraph.Adj i j → (fineEdgeSupport i ∩ fineEdgeSupport j).Nonempty

namespace SigmaPlanckBlockStarSource

lemma support_nonempty
    {ι ε : Type*} [DecidableEq ε] (S : SigmaPlanckBlockStarSource ι ε)
    (i : ι) :
    (S.fineEdgeSupport i).Nonempty := by
  rcases S.support_planck_nonempty i with ⟨e, he, _⟩
  exact ⟨e, he⟩

noncomputable def toSigmaBlockStarCovering
    {ι ε : Type*} [DecidableEq ε] (S : SigmaPlanckBlockStarSource ι ε) :
    SigmaBlockStarCovering ι ε where
  coarseGraph := S.coarseGraph
  fineEdgeSupport := S.fineEdgeSupport
  support_nonempty := S.support_nonempty
  coarse_connected := S.coarse_connected
  adjacent_share_fine_edge := S.adjacent_share_fine_edge

end SigmaPlanckBlockStarSource

abbrev CubeCoord (L : ℕ) := (Fin L × Fin L) × Fin L

abbrev MicroEdgeOffset := (Fin 2 × Fin 2) × Fin 2

abbrev CubeFineEdge (L : ℕ) := CubeCoord L × MicroEdgeOffset

def cubeCoarseGraph (L : ℕ) : SimpleGraph (CubeCoord L) :=
  (SimpleGraph.pathGraph L □ SimpleGraph.pathGraph L) □ SimpleGraph.pathGraph L

def coordInClosedTwoBlock {L : ℕ} (a c : Fin L) : Prop :=
  a = c ∨ c.val + 1 = a.val

def cubeCoordInClosedTwoByTwoByTwoStar {L : ℕ} (a c : CubeCoord L) : Prop :=
  coordInClosedTwoBlock a.1.1 c.1.1 ∧
    coordInClosedTwoBlock a.1.2 c.1.2 ∧
      coordInClosedTwoBlock a.2 c.2

noncomputable def cubeBlockStarSupport (L : ℕ) (c : CubeCoord L) :
    Finset (CubeFineEdge L) := by
  classical
  exact Finset.univ.filter fun e => cubeCoordInClosedTwoByTwoByTwoStar e.1 c

lemma pathGraph_connected_of_four_le (L : ℕ) (hL : 4 ≤ L) :
    (SimpleGraph.pathGraph L).Connected := by
  have h1 : 1 ≤ L := le_trans (by norm_num : 1 ≤ 4) hL
  have hEq : L - 1 + 1 = L := Nat.sub_add_cancel h1
  have hconn := SimpleGraph.pathGraph_connected (L - 1)
  rw [hEq] at hconn
  exact hconn

lemma cubeCoarseGraph_connected (L : ℕ) (hL : 4 ≤ L) :
    (cubeCoarseGraph L).Connected := by
  have hp : (SimpleGraph.pathGraph L).Connected := pathGraph_connected_of_four_le L hL
  exact (hp.boxProd hp).boxProd hp

lemma pathGraph_adj_closedTwoBlock_common {L : ℕ} {i j : Fin L}
    (h : (SimpleGraph.pathGraph L).Adj i j) :
    ∃ a : Fin L, coordInClosedTwoBlock a i ∧ coordInClosedTwoBlock a j := by
  rw [SimpleGraph.pathGraph_adj] at h
  rcases h with h | h
  · exact ⟨j, Or.inr h, Or.inl rfl⟩
  · exact ⟨i, Or.inl rfl, Or.inr h⟩

lemma cubeCoarseGraph_adj_star_common {L : ℕ} {c d : CubeCoord L}
    (h : (cubeCoarseGraph L).Adj c d) :
    ∃ a : CubeCoord L,
      cubeCoordInClosedTwoByTwoByTwoStar a c ∧
        cubeCoordInClosedTwoByTwoByTwoStar a d := by
  rw [cubeCoarseGraph, SimpleGraph.boxProd_adj] at h
  rcases h with hxy_z | hz_xy
  · rcases hxy_z with ⟨hxy, hz⟩
    rw [SimpleGraph.boxProd_adj] at hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨hx, hy⟩
      rcases pathGraph_adj_closedTwoBlock_common hx with ⟨ax, haxc, haxd⟩
      refine ⟨((ax, c.1.2), c.2), ?_⟩
      constructor
      · exact ⟨haxc, Or.inl rfl, Or.inl rfl⟩
      · refine ⟨haxd, ?_, ?_⟩
        · rw [← hy]
          exact Or.inl rfl
        · rw [← hz]
          exact Or.inl rfl
    · rcases hxy with ⟨hy, hx⟩
      rcases pathGraph_adj_closedTwoBlock_common hy with ⟨ay, hayc, hayd⟩
      refine ⟨((c.1.1, ay), c.2), ?_⟩
      constructor
      · exact ⟨Or.inl rfl, hayc, Or.inl rfl⟩
      · refine ⟨?_, hayd, ?_⟩
        · rw [← hx]
          exact Or.inl rfl
        · rw [← hz]
          exact Or.inl rfl
  · rcases hz_xy with ⟨hz, hxy⟩
    rcases pathGraph_adj_closedTwoBlock_common hz with ⟨az, hazc, hazd⟩
    have hx : c.1.1 = d.1.1 := congrArg Prod.fst hxy
    have hy : c.1.2 = d.1.2 := congrArg Prod.snd hxy
    refine ⟨((c.1.1, c.1.2), az), ?_⟩
    constructor
    · exact ⟨Or.inl rfl, Or.inl rfl, hazc⟩
    · refine ⟨?_, ?_, hazd⟩
      · rw [← hx]
        exact Or.inl rfl
      · rw [← hy]
        exact Or.inl rfl

lemma cubeBlockStarSupport_nonempty (L : ℕ) (c : CubeCoord L) :
    (cubeBlockStarSupport L c).Nonempty := by
  refine ⟨(c, ((0, 0), 0)), ?_⟩
  simp [cubeBlockStarSupport, cubeCoordInClosedTwoByTwoByTwoStar,
    coordInClosedTwoBlock]

lemma cubeBlockStarSupport_adjacent_inter_nonempty {L : ℕ} {c d : CubeCoord L}
    (h : (cubeCoarseGraph L).Adj c d) :
    (cubeBlockStarSupport L c ∩ cubeBlockStarSupport L d).Nonempty := by
  rcases cubeCoarseGraph_adj_star_common h with ⟨a, hac, had⟩
  refine ⟨(a, ((0, 0), 0)), ?_⟩
  simp [cubeBlockStarSupport, hac, had]

noncomputable def cubeSigmaBlockStarCovering (L : ℕ) (hL : 4 ≤ L) :
    SigmaBlockStarCovering (CubeCoord L) (CubeFineEdge L) where
  coarseGraph := cubeCoarseGraph L
  fineEdgeSupport := cubeBlockStarSupport L
  support_nonempty := cubeBlockStarSupport_nonempty L
  coarse_connected := cubeCoarseGraph_connected L hL
  adjacent_share_fine_edge := cubeBlockStarSupport_adjacent_inter_nonempty

/--
Source-near finite-support version of the upstream construction:
nonempty block supports produce a row-stochastic block-averaging matrix, hence the
closed block-Laplacian theorem applies to `S = M Mᵀ`.
-/
theorem blockSupportAveraging_blockLaplacian
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty)
    (hconn :
      (supportGraph
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
        (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E))).Connected) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))), 0 ≤ μ) ∧
        ∀ x : ι → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact blockAveragingMatrix_blockLaplacian
    (blockAveragingMatrixFromSupports E)
    (blockAveragingMatrixFromSupports_nonnegative E)
    (blockAveragingMatrixFromSupports_rowStochastic E hnonempty) hconn

theorem blockSupportAveraging_exists_nonzero_spectral_value
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    [Nontrivial ι]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty)
    (hconn :
      (supportGraph
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
        (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E))).Connected) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))) ∧
      μ ≠ 0 := by
  exact blockAveragingMatrix_exists_nonzero_spectral_value
    (blockAveragingMatrixFromSupports E)
    (blockAveragingMatrixFromSupports_nonnegative E)
    (blockAveragingMatrixFromSupports_rowStochastic E hnonempty) hconn

theorem blockSupportAveraging_positive_spectral_gap
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))),
        μ ≠ 0 → γ ≤ μ := by
  exact blockAveragingMatrix_positive_spectral_gap
    (blockAveragingMatrixFromSupports E)
    (blockAveragingMatrixFromSupports_nonnegative E)
    (blockAveragingMatrixFromSupports_rowStochastic E hnonempty)

/-- Canonical Mathlib spectral frame for the symmetrized block-support Laplacian. -/
noncomputable def blockSupportAveragingSymmetrizedSpectralFrame
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) :
    MatrixSpectralFrame
      (similaritySymmetrizedLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports E)))
      ι :=
  similaritySymmetrizedLaplacianSpectralFrame
    (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
    (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E))
    (coarseOverlapMatrix_nonneg
      (blockAveragingMatrixFromSupports E)
      (blockAveragingMatrixFromSupports_nonnegative E))

theorem blockSupportAveraging_canonicalSymmetrizedHeatFlow_decay
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ ι,
        ReducedModalCoefficients
          (blockSupportAveragingSymmetrizedSpectralFrame E).freq
          ((blockSupportAveragingSymmetrizedSpectralFrame E).coords x) →
          γ * modalEnergy
              ((blockSupportAveragingSymmetrizedSpectralFrame E).coords x) ≤
              modalDirichletEnergy
                (blockSupportAveragingSymmetrizedSpectralFrame E).freq
                ((blockSupportAveragingSymmetrizedSpectralFrame E).coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖(blockSupportAveragingSymmetrizedSpectralFrame E).heatFlow t x‖ ^ 2 ≤
                Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  simpa [blockSupportAveragingSymmetrizedSpectralFrame] using
    similaritySymmetrizedLaplacian_canonicalHeatFlow_decay
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))
      (coarseOverlapMatrix_isSymm (blockAveragingMatrixFromSupports E))
      (coarseOverlapMatrix_nonneg
        (blockAveragingMatrixFromSupports E)
        (blockAveragingMatrixFromSupports_nonnegative E))

/--
Block-star support version: nonempty finite block supports and connectivity of
the source-level overlap graph are enough to invoke the closed block-Laplacian
theorem for the induced coarse overlap matrix.
-/
theorem blockStarSupportAveraging_blockLaplacian
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty)
    (hconn : (blockSupportOverlapGraph E).Connected) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))), 0 ≤ μ) ∧
        ∀ x : ι → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact blockSupportAveraging_blockLaplacian E hnonempty
    (blockSupportOverlapGraph_connected_to_supportGraph_connected E hconn)

theorem blockStarSupportAveraging_positive_spectral_gap
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))),
        μ ≠ 0 → γ ≤ μ := by
  exact blockSupportAveraging_positive_spectral_gap E hnonempty

theorem blockStarSupportAveraging_exists_nonzero_spectral_value
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    [Nontrivial ι]
    (E : ι → Finset ε) (hnonempty : ∀ i, (E i).Nonempty)
    (hconn : (blockSupportOverlapGraph E).Connected) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports E))) ∧
      μ ≠ 0 := by
  exact blockSupportAveraging_exists_nonzero_spectral_value E hnonempty
    (blockSupportOverlapGraph_connected_to_supportGraph_connected E hconn)

/--
Sigma block-star covering version: the source-level connected coarse graph and
fine-edge overlap of adjacent block stars generate the finite supports needed by
the closed block-Laplacian theorem.
-/
theorem sigmaBlockStarCovering_blockLaplacian
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport))), 0 ≤ μ) ∧
        ∀ x : ι → ℝ,
          ((randomWalkLaplacian
              (coarseOverlapMatrix
                (blockAveragingMatrixFromSupports C.fineEdgeSupport))).mulVec x) =
            0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact blockStarSupportAveraging_blockLaplacian C.fineEdgeSupport C.support_nonempty
    C.overlapGraph_connected

theorem sigmaBlockStarCovering_positive_spectral_gap
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport))),
        μ ≠ 0 → γ ≤ μ := by
  exact blockStarSupportAveraging_positive_spectral_gap
    C.fineEdgeSupport C.support_nonempty

theorem sigmaBlockStarCovering_exists_nonzero_spectral_value
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    [Nontrivial ι]
    (C : SigmaBlockStarCovering ι ε) :
    ∃ μ : ℝ, μ ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport))) ∧
      μ ≠ 0 := by
  exact blockStarSupportAveraging_exists_nonzero_spectral_value
    C.fineEdgeSupport C.support_nonempty C.overlapGraph_connected

theorem sigmaBlockStarCovering_modal_poincare_decay
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalHeatEnergy μ t a ≤ Real.exp (-2 * γ * t) * modalEnergy a := by
  rcases sigmaBlockStarCovering_positive_spectral_gap C with ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro a hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (μ k) (hspec k) hne)
  · intro t ht
    exact modal_heat_energy_decay hreduced
      (fun k hne => hgap (μ k) (hspec k) hne) ht

theorem sigmaBlockStarCovering_diagonalHeatFlow_decay
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalEnergy (diagonalHeatFlow μ t a) ≤
              Real.exp (-2 * γ * t) * modalEnergy a := by
  rcases sigmaBlockStarCovering_positive_spectral_gap C with ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro a hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (μ k) (hspec k) hne)
  · intro t ht
    exact diagonalHeatFlow_energy_decay hreduced
      (fun k hne => hgap (μ k) (hspec k) hne) ht

theorem sigmaBlockStarCovering_spectralFrame_heatFlow_decay
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε)
    {κ : Type*} [Fintype κ]
    (F :
      MatrixSpectralFrame
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport)))
        κ)
    (hspec : ∀ k, F.freq k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ ι, ReducedModalCoefficients F.freq (F.coords x) →
        γ * modalEnergy (F.coords x) ≤ modalDirichletEnergy F.freq (F.coords x) ∧
          ∀ t : ℝ, 0 ≤ t →
            ‖F.heatFlow t x‖ ^ 2 ≤ Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  rcases sigmaBlockStarCovering_positive_spectral_gap C with ⟨γ, hγpos, hgap⟩
  refine ⟨γ, hγpos, ?_⟩
  intro x hreduced
  refine ⟨?_, ?_⟩
  · exact modal_poincare hreduced (fun k hne => hgap (F.freq k) (hspec k) hne)
  · intro t ht
    exact F.heatFlow_energy_decay hreduced
      (fun k hne => hgap (F.freq k) (hspec k) hne) ht

/-- Canonical Mathlib spectral frame for a block-star covering's symmetrized Laplacian. -/
noncomputable def sigmaBlockStarCoveringSymmetrizedSpectralFrame
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε) :
    MatrixSpectralFrame
      (similaritySymmetrizedLaplacian
        (coarseOverlapMatrix (blockAveragingMatrixFromSupports C.fineEdgeSupport)))
      ι :=
  blockSupportAveragingSymmetrizedSpectralFrame C.fineEdgeSupport

theorem sigmaBlockStarCovering_canonicalSymmetrizedHeatFlow_decay
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (C : SigmaBlockStarCovering ι ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ ι,
        ReducedModalCoefficients
          (sigmaBlockStarCoveringSymmetrizedSpectralFrame C).freq
          ((sigmaBlockStarCoveringSymmetrizedSpectralFrame C).coords x) →
          γ * modalEnergy
              ((sigmaBlockStarCoveringSymmetrizedSpectralFrame C).coords x) ≤
              modalDirichletEnergy
                (sigmaBlockStarCoveringSymmetrizedSpectralFrame C).freq
                ((sigmaBlockStarCoveringSymmetrizedSpectralFrame C).coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖(sigmaBlockStarCoveringSymmetrizedSpectralFrame C).heatFlow t x‖ ^ 2 ≤
                Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  simpa [sigmaBlockStarCoveringSymmetrizedSpectralFrame] using
    blockSupportAveraging_canonicalSymmetrizedHeatFlow_decay C.fineEdgeSupport

namespace SigmaPlanckBlockStarSource

theorem blockLaplacian
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (S : SigmaPlanckBlockStarSource ι ε) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix (blockAveragingMatrixFromSupports S.fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports S.fineEdgeSupport))),
          0 ≤ μ) ∧
        ∀ x : ι → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports S.fineEdgeSupport))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact sigmaBlockStarCovering_blockLaplacian S.toSigmaBlockStarCovering

theorem positive_spectral_gap
    {ι ε : Type*} [Fintype ι] [DecidableEq ι] [Fintype ε] [DecidableEq ε]
    (S : SigmaPlanckBlockStarSource ι ε) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix (blockAveragingMatrixFromSupports S.fineEdgeSupport))),
        μ ≠ 0 → γ ≤ μ := by
  exact sigmaBlockStarCovering_positive_spectral_gap S.toSigmaBlockStarCovering

end SigmaPlanckBlockStarSource

theorem cubeSigmaBlockStarCovering_blockLaplacian (L : ℕ) (hL : 4 ≤ L) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (cubeSigmaBlockStarCovering L hL).fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (cubeSigmaBlockStarCovering L hL).fineEdgeSupport))), 0 ≤ μ) ∧
        ∀ x : CubeCoord L → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports
                (cubeSigmaBlockStarCovering L hL).fineEdgeSupport))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact sigmaBlockStarCovering_blockLaplacian (cubeSigmaBlockStarCovering L hL)

theorem cubeSigmaBlockStarCovering_positive_spectral_gap (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (cubeSigmaBlockStarCovering L hL).fineEdgeSupport))),
        μ ≠ 0 → γ ≤ μ := by
  exact sigmaBlockStarCovering_positive_spectral_gap (cubeSigmaBlockStarCovering L hL)

abbrev SigmaCoord4 (L : ℕ) := CubeCoord L × Fin L

lemma sigmaCoord4_nontrivial_of_four_le (L : ℕ) (hL : 4 ≤ L) :
    Nontrivial (SigmaCoord4 L) := by
  haveI : Nontrivial (Fin L) :=
    Fin.nontrivial_iff_two_le.mpr (le_trans (by norm_num : 2 ≤ 4) hL)
  infer_instance

def sigmaCoarseGraph4 (L : ℕ) : SimpleGraph (SigmaCoord4 L) :=
  cubeCoarseGraph L □ SimpleGraph.pathGraph L

def sigmaCoord4Get {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4) : Fin L := by
  exact
    if axis = 0 then x.1.1.1
    else if axis = 1 then x.1.1.2
    else if axis = 2 then x.1.2
    else x.2

def sigmaCoord4Set {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4)
    (v : Fin L) : SigmaCoord4 L := by
  exact
    if axis = 0 then (((v, x.1.1.2), x.1.2), x.2)
    else if axis = 1 then (((x.1.1.1, v), x.1.2), x.2)
    else if axis = 2 then (((x.1.1.1, x.1.1.2), v), x.2)
    else (x.1, v)

def sigmaCoordInClosedTwoByTwoByTwoByTwoStar {L : ℕ}
    (a c : SigmaCoord4 L) : Prop :=
  cubeCoordInClosedTwoByTwoByTwoStar a.1 c.1 ∧
    coordInClosedTwoBlock a.2 c.2

abbrev SigmaFineEdgeData4 (L : ℕ) := (SigmaCoord4 L × Fin 4) × Bool

def SigmaFineEdgeValid4 {L : ℕ} (e : SigmaFineEdgeData4 L) : Prop :=
  if e.2 then (sigmaCoord4Get e.1.1 e.1.2).val + 1 < L
  else 0 < (sigmaCoord4Get e.1.1 e.1.2).val

abbrev SigmaFineEdge4 (L : ℕ) := { e : SigmaFineEdgeData4 L // SigmaFineEdgeValid4 e }

noncomputable instance sigmaFineEdge4DecidableEq (L : ℕ) :
    DecidableEq (SigmaFineEdge4 L) := by
  classical
  exact inferInstance

noncomputable instance sigmaFineEdge4Fintype (L : ℕ) : Fintype (SigmaFineEdge4 L) := by
  classical
  exact inferInstance

def sigmaFineEdgeSource {L : ℕ} (e : SigmaFineEdge4 L) : SigmaCoord4 L :=
  e.1.1.1

def sigmaFineEdgeAxis {L : ℕ} (e : SigmaFineEdge4 L) : Fin 4 :=
  e.1.1.2

def sigmaFineEdgeForward {L : ℕ} (e : SigmaFineEdge4 L) : Bool :=
  e.1.2

def sigmaFineEdgeStepTarget {L : ℕ} (e : SigmaFineEdge4 L) : Fin L := by
  by_cases hf : e.1.2 = true
  · exact
      ⟨(sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)).val + 1,
        by
          simpa [sigmaFineEdgeForward, sigmaFineEdgeAxis, sigmaFineEdgeSource,
            SigmaFineEdgeValid4, hf] using e.2⟩
  · exact
      ⟨(sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)).val - 1,
        by
          exact lt_of_le_of_lt
            (Nat.sub_le _ _)
            (sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)).isLt⟩

def sigmaFineEdgeTarget {L : ℕ} (e : SigmaFineEdge4 L) : SigmaCoord4 L :=
  sigmaCoord4Set (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)
    (sigmaFineEdgeStepTarget e)

lemma sigmaCoord4Get_set_same {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4)
    (v : Fin L) :
    sigmaCoord4Get (sigmaCoord4Set x axis v) axis = v := by
  fin_cases axis <;> simp [sigmaCoord4Get, sigmaCoord4Set]

lemma sigmaCoord4Set_get_same {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4) :
    sigmaCoord4Set x axis (sigmaCoord4Get x axis) = x := by
  fin_cases axis <;> simp [sigmaCoord4Get, sigmaCoord4Set]

lemma sigmaCoord4Set_set_same {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4)
    (v w : Fin L) :
    sigmaCoord4Set (sigmaCoord4Set x axis v) axis w =
      sigmaCoord4Set x axis w := by
  fin_cases axis <;> simp [sigmaCoord4Set]

lemma sigmaFineEdgeTarget_get_axis {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaCoord4Get (sigmaFineEdgeTarget e) (sigmaFineEdgeAxis e) =
      sigmaFineEdgeStepTarget e := by
  simp [sigmaFineEdgeTarget, sigmaCoord4Get_set_same]

lemma sigmaFineEdgeStepTarget_val_forward {L : ℕ} (e : SigmaFineEdge4 L)
    (hf : sigmaFineEdgeForward e = true) :
    (sigmaFineEdgeStepTarget e).val =
      (sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)).val + 1 := by
  have hraw : e.1.2 = true := by
    simpa [sigmaFineEdgeForward] using hf
  simp [sigmaFineEdgeStepTarget, sigmaFineEdgeSource,
    sigmaFineEdgeAxis, hraw]

lemma sigmaFineEdgeStepTarget_val_backward {L : ℕ} (e : SigmaFineEdge4 L)
    (hf : sigmaFineEdgeForward e = false) :
    (sigmaFineEdgeStepTarget e).val =
      (sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e)).val - 1 := by
  have hraw : e.1.2 = false := by
    simpa [sigmaFineEdgeForward] using hf
  simp [sigmaFineEdgeStepTarget, sigmaFineEdgeSource, sigmaFineEdgeAxis, hraw]

def sigmaFineEdgeReverse {L : ℕ} (e : SigmaFineEdge4 L) :
    SigmaFineEdge4 L := by
  refine ⟨((sigmaFineEdgeTarget e, sigmaFineEdgeAxis e),
    !sigmaFineEdgeForward e), ?_⟩
  by_cases hf : sigmaFineEdgeForward e = true
  · have hpos : 0 <
        (sigmaCoord4Get (sigmaFineEdgeTarget e)
          (sigmaFineEdgeAxis e)).val := by
      rw [sigmaFineEdgeTarget_get_axis e,
        sigmaFineEdgeStepTarget_val_forward e hf]
      exact Nat.succ_pos _
    have hraw : e.1.2 = true := by
      simpa [sigmaFineEdgeForward] using hf
    simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using hpos
  · have hfalse : sigmaFineEdgeForward e = false := by
      exact Bool.eq_false_of_not_eq_true hf
    have hraw : e.1.2 = false := by
      simpa [sigmaFineEdgeForward] using hfalse
    have hsource_pos :
        0 < (sigmaCoord4Get (sigmaFineEdgeSource e)
          (sigmaFineEdgeAxis e)).val := by
      simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using e.2
    have hlt :
        (sigmaCoord4Get (sigmaFineEdgeTarget e)
          (sigmaFineEdgeAxis e)).val + 1 < L := by
      rw [sigmaFineEdgeTarget_get_axis e,
        sigmaFineEdgeStepTarget_val_backward e hfalse,
        Nat.sub_add_cancel hsource_pos]
      exact (sigmaCoord4Get (sigmaFineEdgeSource e)
        (sigmaFineEdgeAxis e)).isLt
    simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using hlt

lemma sigmaFineEdgeReverse_source {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeSource (sigmaFineEdgeReverse e) = sigmaFineEdgeTarget e := by
  simp [sigmaFineEdgeReverse, sigmaFineEdgeSource]

lemma sigmaFineEdgeReverse_axis {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeAxis (sigmaFineEdgeReverse e) = sigmaFineEdgeAxis e := by
  simp [sigmaFineEdgeReverse, sigmaFineEdgeAxis]

lemma sigmaFineEdgeReverse_forward {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeForward (sigmaFineEdgeReverse e) =
      !sigmaFineEdgeForward e := by
  simp [sigmaFineEdgeReverse, sigmaFineEdgeForward]

lemma sigmaFineEdgeReverse_stepTarget {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeStepTarget (sigmaFineEdgeReverse e) =
      sigmaCoord4Get (sigmaFineEdgeSource e) (sigmaFineEdgeAxis e) := by
  apply Fin.ext
  by_cases hf : sigmaFineEdgeForward e = true
  · have hrev_false : sigmaFineEdgeForward (sigmaFineEdgeReverse e) = false := by
      simp [sigmaFineEdgeReverse_forward, hf]
    have hsrc :
        (sigmaCoord4Get (sigmaFineEdgeSource (sigmaFineEdgeReverse e))
          (sigmaFineEdgeAxis (sigmaFineEdgeReverse e))).val =
          (sigmaCoord4Get (sigmaFineEdgeSource e)
            (sigmaFineEdgeAxis e)).val + 1 := by
      rw [sigmaFineEdgeReverse_source, sigmaFineEdgeReverse_axis,
        sigmaFineEdgeTarget_get_axis e,
        sigmaFineEdgeStepTarget_val_forward e hf]
    rw [sigmaFineEdgeStepTarget_val_backward (sigmaFineEdgeReverse e)
      hrev_false, hsrc]
    exact Nat.add_sub_cancel _ _
  · have hfalse : sigmaFineEdgeForward e = false :=
      Bool.eq_false_of_not_eq_true hf
    have hrev_true : sigmaFineEdgeForward (sigmaFineEdgeReverse e) = true := by
      simp [sigmaFineEdgeReverse_forward, hfalse]
    have hsource_pos :
        0 < (sigmaCoord4Get (sigmaFineEdgeSource e)
          (sigmaFineEdgeAxis e)).val := by
      have hraw : e.1.2 = false := by
        simpa [sigmaFineEdgeForward] using hfalse
      simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using e.2
    have hsrc :
        (sigmaCoord4Get (sigmaFineEdgeSource (sigmaFineEdgeReverse e))
          (sigmaFineEdgeAxis (sigmaFineEdgeReverse e))).val =
          (sigmaCoord4Get (sigmaFineEdgeSource e)
            (sigmaFineEdgeAxis e)).val - 1 := by
      rw [sigmaFineEdgeReverse_source, sigmaFineEdgeReverse_axis,
        sigmaFineEdgeTarget_get_axis e,
        sigmaFineEdgeStepTarget_val_backward e hfalse]
    rw [sigmaFineEdgeStepTarget_val_forward (sigmaFineEdgeReverse e)
      hrev_true, hsrc, Nat.sub_add_cancel hsource_pos]

lemma sigmaFineEdgeReverse_target {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeTarget (sigmaFineEdgeReverse e) = sigmaFineEdgeSource e := by
  rw [sigmaFineEdgeTarget, sigmaFineEdgeReverse_source,
    sigmaFineEdgeReverse_axis, sigmaFineEdgeReverse_stepTarget e]
  rw [sigmaFineEdgeTarget, sigmaCoord4Set_set_same,
    sigmaCoord4Set_get_same]

abbrev SigmaCurvatureField4 (L : ℕ) := SigmaFineEdge4 L → ℝ

noncomputable def sigmaFineEdgeAtSource (L : ℕ) (hL : 4 ≤ L)
    (s : SigmaCoord4 L) : SigmaFineEdge4 L := by
  classical
  by_cases hstep : (sigmaCoord4Get s 0).val + 1 < L
  · exact ⟨((s, 0), true), by simp [SigmaFineEdgeValid4, hstep]⟩
  · have hpos : 0 < (sigmaCoord4Get s 0).val := by
      by_contra hnot
      have hzero : (sigmaCoord4Get s 0).val = 0 := Nat.eq_zero_of_not_pos hnot
      have hlt : (sigmaCoord4Get s 0).val + 1 < L := by
        have h1 : 1 < L := lt_of_lt_of_le (by norm_num : 1 < 4) hL
        simpa [hzero] using h1
      exact hstep hlt
    exact ⟨((s, 0), false), by simpa [SigmaFineEdgeValid4, hstep] using hpos⟩

lemma sigmaFineEdgeAtSource_source (L : ℕ) (hL : 4 ≤ L)
    (s : SigmaCoord4 L) :
    sigmaFineEdgeSource (sigmaFineEdgeAtSource L hL s) = s := by
  unfold sigmaFineEdgeAtSource
  by_cases hstep : (sigmaCoord4Get s 0).val + 1 < L
  · simp [sigmaFineEdgeSource, hstep]
  · simp [sigmaFineEdgeSource, hstep]

noncomputable def sigmaBlockStarSupport4 (L : ℕ) (_hL : 4 ≤ L)
    (c : SigmaCoord4 L) : Finset (SigmaFineEdge4 L) := by
  classical
  exact Finset.univ.filter fun e =>
    sigmaCoordInClosedTwoByTwoByTwoByTwoStar (sigmaFineEdgeSource e) c

lemma sigmaCoarseGraph4_connected (L : ℕ) (hL : 4 ≤ L) :
    (sigmaCoarseGraph4 L).Connected := by
  have hc : (cubeCoarseGraph L).Connected := cubeCoarseGraph_connected L hL
  have hp : (SimpleGraph.pathGraph L).Connected := pathGraph_connected_of_four_le L hL
  exact hc.boxProd hp

lemma sigmaCoarseGraph4_adj_star_common {L : ℕ} {c d : SigmaCoord4 L}
    (h : (sigmaCoarseGraph4 L).Adj c d) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInClosedTwoByTwoByTwoByTwoStar a c ∧
        sigmaCoordInClosedTwoByTwoByTwoByTwoStar a d := by
  rw [sigmaCoarseGraph4, SimpleGraph.boxProd_adj] at h
  rcases h with hcube_w | hw_cube
  · rcases hcube_w with ⟨hcube, hw⟩
    rcases cubeCoarseGraph_adj_star_common hcube with ⟨a, hac, had⟩
    refine ⟨(a, c.2), ?_⟩
    constructor
    · exact ⟨hac, Or.inl rfl⟩
    · refine ⟨had, ?_⟩
      rw [← hw]
      exact Or.inl rfl
  · rcases hw_cube with ⟨hw, hcube⟩
    rcases pathGraph_adj_closedTwoBlock_common hw with ⟨a, hac, had⟩
    refine ⟨(c.1, a), ?_⟩
    constructor
    · exact ⟨by
        rw [cubeCoordInClosedTwoByTwoByTwoStar]
        exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩, hac⟩
    · refine ⟨?_, had⟩
      rw [← hcube]
      rw [cubeCoordInClosedTwoByTwoByTwoStar]
      exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

lemma sigmaBlockStarSupport4_nonempty (L : ℕ) (hL : 4 ≤ L)
    (c : SigmaCoord4 L) :
    (sigmaBlockStarSupport4 L hL c).Nonempty := by
  refine ⟨sigmaFineEdgeAtSource L hL c, ?_⟩
  have hs := sigmaFineEdgeAtSource_source L hL c
  simp [sigmaBlockStarSupport4, hs, sigmaCoordInClosedTwoByTwoByTwoByTwoStar,
    cubeCoordInClosedTwoByTwoByTwoStar, coordInClosedTwoBlock]

lemma sigmaBlockStarSupport4_adjacent_inter_nonempty {L : ℕ} (hL : 4 ≤ L)
    {c d : SigmaCoord4 L} (h : (sigmaCoarseGraph4 L).Adj c d) :
    (sigmaBlockStarSupport4 L hL c ∩ sigmaBlockStarSupport4 L hL d).Nonempty := by
  rcases sigmaCoarseGraph4_adj_star_common h with ⟨a, hac, had⟩
  refine ⟨sigmaFineEdgeAtSource L hL a, ?_⟩
  have hs := sigmaFineEdgeAtSource_source L hL a
  simp [sigmaBlockStarSupport4, hs, hac, had]

noncomputable def sigma4BlockStarCovering (L : ℕ) (hL : 4 ≤ L) :
    SigmaBlockStarCovering (SigmaCoord4 L) (SigmaFineEdge4 L) where
  coarseGraph := sigmaCoarseGraph4 L
  fineEdgeSupport := sigmaBlockStarSupport4 L hL
  support_nonempty := sigmaBlockStarSupport4_nonempty L hL
  coarse_connected := sigmaCoarseGraph4_connected L hL
  adjacent_share_fine_edge := sigmaBlockStarSupport4_adjacent_inter_nonempty hL

/-- Concrete random-walk Laplacian generated by the 4D Sigma block-star covering. -/
noncomputable def sigma4BlockStarRandomWalkLaplacian (L : ℕ) :
    Matrix (SigmaCoord4 L) (SigmaCoord4 L) ℝ :=
  if hL : 4 ≤ L then
    randomWalkLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (sigma4BlockStarCovering L hL).fineEdgeSupport))
  else 0

noncomputable def sigma4BlockStarLaplacianFamily : BoundaryLaplacianFamily where
  Node := SigmaCoord4
  nodeFintype := by
    intro L
    infer_instance
  nodeDecidableEq := by
    intro L
    infer_instance
  laplacian := sigma4BlockStarRandomWalkLaplacian

lemma sigma4BlockStarRandomWalkLaplacian_of_four_le (L : ℕ) (hL : 4 ≤ L) :
    sigma4BlockStarRandomWalkLaplacian L =
      randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4BlockStarCovering L hL).fineEdgeSupport)) := by
  unfold sigma4BlockStarRandomWalkLaplacian
  simp [hL]

theorem sigma4BlockStarLaplacianFamily_spectrum_nonneg (L : ℕ) (hL : 4 ≤ L) :
    ∀ μ ∈ sigma4BlockStarLaplacianFamily.spectralSet L, 0 ≤ μ := by
  have hnonneg := (sigmaBlockStarCovering_blockLaplacian (sigma4BlockStarCovering L hL)).2.1
  intro μ hμ
  exact hnonneg μ (by
    simpa [BoundaryLaplacianFamily.spectralSet, sigma4BlockStarLaplacianFamily,
      sigma4BlockStarRandomWalkLaplacian, hL] using hμ)

theorem sigma4BlockStarLaplacianFamily_positive_spectral_gap
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ sigma4BlockStarLaplacianFamily.spectralSet L, μ ≠ 0 → γ ≤ μ := by
  have hgap := sigmaBlockStarCovering_positive_spectral_gap (sigma4BlockStarCovering L hL)
  simpa [BoundaryLaplacianFamily.spectralSet, sigma4BlockStarLaplacianFamily,
    sigma4BlockStarRandomWalkLaplacian, hL] using hgap

theorem sigma4BlockStarLaplacianFamily_exists_nonzero_spectral_value
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ μ : ℝ, μ ∈ sigma4BlockStarLaplacianFamily.spectralSet L ∧ μ ≠ 0 := by
  haveI : Nontrivial (SigmaCoord4 L) := sigmaCoord4_nontrivial_of_four_le L hL
  have hnonzero :=
    sigmaBlockStarCovering_exists_nonzero_spectral_value (sigma4BlockStarCovering L hL)
  simpa [BoundaryLaplacianFamily.spectralSet, sigma4BlockStarLaplacianFamily,
    sigma4BlockStarRandomWalkLaplacian, hL] using hnonzero

/-- The existing finite `Fin L` Sigma construction is the open-boundary family. -/
noncomputable abbrev sigma4BlockStarOpenLaplacianFamily : BoundaryLaplacianFamily :=
  sigma4BlockStarLaplacianFamily

noncomputable def sigma4BlockStarOpenSpectrallyClosedFamily :
    SpectrallyClosedBoundaryLaplacianFamily where
  family := sigma4BlockStarOpenLaplacianFamily
  spectrum_nonneg := by
    intro L hL
    exact sigma4BlockStarLaplacianFamily_spectrum_nonneg L hL
  positive_spectral_gap := by
    intro L hL
    exact sigma4BlockStarLaplacianFamily_positive_spectral_gap L hL

noncomputable def sigma4BlockStarOpenNonzeroSpectralValueExistsFrom :
    BoundaryNonzeroSpectralValueExistsFrom sigma4BlockStarOpenLaplacianFamily 4 where
  L0_ge_four := le_rfl
  exists_nonzero := by
    intro L hL
    exact sigma4BlockStarLaplacianFamily_exists_nonzero_spectral_value L hL

/-- Concrete open-boundary spectral programme for the Sigma block-star family. -/
structure Sigma4OpenSpectralLimitProgram where
  openLambda : ℕ → ℝ
  openRealization :
    BoundarySpectralValueRealization sigma4BlockStarOpenLaplacianFamily openLambda
  openLimit : RescaledInverseSquareLimitCertificate openLambda

namespace Sigma4OpenSpectralLimitProgram

noncomputable def openScaling (P : Sigma4OpenSpectralLimitProgram) :
    InverseSquareSpectralScaling P.openLambda :=
  inverseSquareSpectralScaling_of_rescaled_tendsto P.openLimit

theorem open_value_mem (P : Sigma4OpenSpectralLimitProgram) (L : ℕ) :
    P.openLambda L ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L :=
  P.openRealization.value_mem L

theorem open_first_nonzero (P : Sigma4OpenSpectralLimitProgram) (L : ℕ) :
    ∀ μ ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L,
      μ ≠ 0 → P.openLambda L ≤ μ :=
  P.openRealization.first_nonzero L

end Sigma4OpenSpectralLimitProgram

/--
Sigma boundary spectral programme with the concrete open family and a supplied
periodic family.
-/
structure Sigma4BoundarySpectralLimitProgram where
  periodic : SpectrallyClosedBoundaryLaplacianFamily
  periodicLambda : ℕ → ℝ
  openLambda : ℕ → ℝ
  periodicRealization : BoundarySpectralValueRealization periodic.family periodicLambda
  openRealization :
    BoundarySpectralValueRealization sigma4BlockStarOpenLaplacianFamily openLambda
  limit : BoundaryContinuumLimitCertificate periodicLambda openLambda

namespace Sigma4BoundarySpectralLimitProgram

noncomputable def toBoundarySpectralLimitProgram
    (P : Sigma4BoundarySpectralLimitProgram) : BoundarySpectralLimitProgram where
  periodicFamily := P.periodic.family
  openFamily := sigma4BlockStarOpenLaplacianFamily
  periodicLambda := P.periodicLambda
  openLambda := P.openLambda
  periodicRealization := P.periodicRealization
  openRealization := P.openRealization
  limit := P.limit

noncomputable def periodicScaling (P : Sigma4BoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.periodicLambda :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling (P : Sigma4BoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.openLambda :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK (P : Sigma4BoundarySpectralLimitProgram) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0 (P : Sigma4BoundarySpectralLimitProgram) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound (P : Sigma4BoundarySpectralLimitProgram) :
    BoundaryDifferenceInverseSquareBound P.periodicLambda P.openLambda
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

theorem open_value_mem (P : Sigma4BoundarySpectralLimitProgram) (L : ℕ) :
    P.openLambda L ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L :=
  P.openRealization.value_mem L

theorem periodic_value_mem (P : Sigma4BoundarySpectralLimitProgram) (L : ℕ) :
    P.periodicLambda L ∈ P.periodic.family.spectralSet L :=
  P.periodicRealization.value_mem L

end Sigma4BoundarySpectralLimitProgram

/-- Cycle graph on `Fin L`, containing the path edges and the wrap-around edge. -/
def finCycleGraph (L : ℕ) : SimpleGraph (Fin L) where
  Adj i j := i ≠ j ∧
    ((SimpleGraph.pathGraph L).Adj i j ∨
      (i.val = 0 ∧ j.val + 1 = L) ∨
        (j.val = 0 ∧ i.val + 1 = L))
  symm := by
    intro i j hij
    refine ⟨hij.1.symm, ?_⟩
    rcases hij.2 with hpath | hwrap | hwrap
    · exact Or.inl hpath.symm
    · exact Or.inr (Or.inr ⟨hwrap.1, hwrap.2⟩)
    · exact Or.inr (Or.inl ⟨hwrap.1, hwrap.2⟩)

lemma pathGraph_le_finCycleGraph (L : ℕ) :
    SimpleGraph.pathGraph L ≤ finCycleGraph L := by
  intro i j hij
  exact ⟨hij.ne, Or.inl hij⟩

lemma finCycleGraph_connected_of_four_le (L : ℕ) (hL : 4 ≤ L) :
    (finCycleGraph L).Connected :=
  (pathGraph_connected_of_four_le L hL).mono (pathGraph_le_finCycleGraph L)

def coordInPeriodicClosedTwoBlock {L : ℕ} (a c : Fin L) : Prop :=
  a = c ∨ c.val + 1 = a.val ∨ (c.val + 1 = L ∧ a.val = 0)

def coordPeriodicNext {L : ℕ} (c : Fin L) : Fin L := by
  by_cases hnext : c.val + 1 < L
  · exact ⟨c.val + 1, hnext⟩
  · exact ⟨0, lt_of_le_of_lt (Nat.zero_le c.val) c.isLt⟩

def coordPeriodicPrev {L : ℕ} (c : Fin L) : Fin L := by
  by_cases hpos : 0 < c.val
  · exact ⟨c.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) c.isLt⟩
  · exact
      ⟨L - 1,
        Nat.sub_lt (lt_of_le_of_lt (Nat.zero_le c.val) c.isLt)
          (by norm_num)⟩

lemma coordPeriodicNext_val_of_lt {L : ℕ} {c : Fin L}
    (h : c.val + 1 < L) :
    (coordPeriodicNext c).val = c.val + 1 := by
  simp [coordPeriodicNext, h]

lemma coordPeriodicNext_val_of_not_lt {L : ℕ} {c : Fin L}
    (h : ¬ c.val + 1 < L) :
    (coordPeriodicNext c).val = 0 := by
  simp [coordPeriodicNext, h]

lemma coordPeriodicPrev_val_of_pos {L : ℕ} {c : Fin L}
    (h : 0 < c.val) :
    (coordPeriodicPrev c).val = c.val - 1 := by
  simp [coordPeriodicPrev, h]

lemma coordPeriodicPrev_val_of_not_pos {L : ℕ} {c : Fin L}
    (h : ¬ 0 < c.val) :
    (coordPeriodicPrev c).val = L - 1 := by
  simp [coordPeriodicPrev, h]

lemma coordPeriodicNext_ne_self {L : ℕ} (hL : 2 ≤ L) (c : Fin L) :
    coordPeriodicNext c ≠ c := by
  intro h
  have hval := congrArg Fin.val h
  unfold coordPeriodicNext at hval
  by_cases hnext : c.val + 1 < L
  · simp [hnext] at hval
  · simp [hnext] at hval
    have hlast : c.val + 1 = L := by omega
    omega

lemma coordInPeriodicClosedTwoBlock_iff_eq_or_next {L : ℕ}
    (a c : Fin L) :
    coordInPeriodicClosedTwoBlock a c ↔ a = c ∨ a = coordPeriodicNext c := by
  unfold coordInPeriodicClosedTwoBlock coordPeriodicNext
  by_cases hnext : c.val + 1 < L
  · have hnotlast : c.val + 1 ≠ L := by omega
    constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Fin.ext (by simpa [hnext] using h.symm))
      · exact False.elim (hnotlast h.1)
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl (by simpa [hnext] using congrArg Fin.val h.symm))
  · have hlast : c.val + 1 = L := by omega
    constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inl h
      · exact False.elim (by omega)
      · exact Or.inr (Fin.ext (by simpa [hnext] using h.2))
    · intro h
      rcases h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inr ⟨hlast, by simpa [hnext] using congrArg Fin.val h⟩)

noncomputable def coordPeriodicClosedTwoBlockSet (L : ℕ) (c : Fin L) :
    Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun a => coordInPeriodicClosedTwoBlock a c

lemma coordPeriodicClosedTwoBlockSet_mem {L : ℕ} (a c : Fin L) :
    a ∈ coordPeriodicClosedTwoBlockSet L c ↔
      coordInPeriodicClosedTwoBlock a c := by
  classical
  simp [coordPeriodicClosedTwoBlockSet]

lemma coordPeriodicClosedTwoBlockSet_eq_pair {L : ℕ} (c : Fin L) :
    coordPeriodicClosedTwoBlockSet L c = {c, coordPeriodicNext c} := by
  classical
  ext a
  rw [coordPeriodicClosedTwoBlockSet_mem,
    coordInPeriodicClosedTwoBlock_iff_eq_or_next]
  simp [eq_comm]

lemma coordPeriodicClosedTwoBlockSet_card_eq_two {L : ℕ}
    (hL : 2 ≤ L) (c : Fin L) :
    (coordPeriodicClosedTwoBlockSet L c).card = 2 := by
  classical
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  have hne : c ≠ coordPeriodicNext c := (coordPeriodicNext_ne_self hL c).symm
  simp [hne]

lemma coordPeriodicPrev_ne_self {L : ℕ} (hL : 2 ≤ L) (c : Fin L) :
    coordPeriodicPrev c ≠ c := by
  intro h
  have hval := congrArg Fin.val h
  unfold coordPeriodicPrev at hval
  by_cases hpos : 0 < c.val
  · simp [hpos] at hval
    omega
  · simp [hpos] at hval
    omega

lemma coordPeriodicNext_next_ne_self {L : ℕ} (hL : 3 ≤ L) (c : Fin L) :
    coordPeriodicNext (coordPeriodicNext c) ≠ c := by
  intro h
  have hval := congrArg Fin.val h
  by_cases h1 : c.val + 1 < L
  · have hnval : (coordPeriodicNext c).val = c.val + 1 :=
      coordPeriodicNext_val_of_lt h1
    by_cases h2 : (coordPeriodicNext c).val + 1 < L
    · have hnnval : (coordPeriodicNext (coordPeriodicNext c)).val =
          (coordPeriodicNext c).val + 1 :=
        coordPeriodicNext_val_of_lt h2
      omega
    · have hnnval : (coordPeriodicNext (coordPeriodicNext c)).val = 0 :=
        coordPeriodicNext_val_of_not_lt h2
      omega
  · have hnval : (coordPeriodicNext c).val = 0 :=
      coordPeriodicNext_val_of_not_lt h1
    by_cases h2 : (coordPeriodicNext c).val + 1 < L
    · have hnnval : (coordPeriodicNext (coordPeriodicNext c)).val =
          (coordPeriodicNext c).val + 1 :=
        coordPeriodicNext_val_of_lt h2
      omega
    · have hnnval : (coordPeriodicNext (coordPeriodicNext c)).val = 0 :=
        coordPeriodicNext_val_of_not_lt h2
      omega

lemma coordPeriodicNext_prev {L : ℕ} (c : Fin L) :
    coordPeriodicNext (coordPeriodicPrev c) = c := by
  ext
  by_cases hpos : 0 < c.val
  · have hpval : (coordPeriodicPrev c).val = c.val - 1 :=
      coordPeriodicPrev_val_of_pos hpos
    have hnext : (coordPeriodicPrev c).val + 1 < L := by omega
    have hnval : (coordPeriodicNext (coordPeriodicPrev c)).val =
        (coordPeriodicPrev c).val + 1 :=
      coordPeriodicNext_val_of_lt hnext
    omega
  · have hzero : c.val = 0 := Nat.eq_zero_of_not_pos hpos
    have hpval : (coordPeriodicPrev c).val = L - 1 :=
      coordPeriodicPrev_val_of_not_pos hpos
    have hnext : ¬ (coordPeriodicPrev c).val + 1 < L := by omega
    have hnval : (coordPeriodicNext (coordPeriodicPrev c)).val = 0 :=
      coordPeriodicNext_val_of_not_lt hnext
    omega

lemma coordPeriodicPrev_next {L : ℕ} (c : Fin L) :
    coordPeriodicPrev (coordPeriodicNext c) = c := by
  ext
  by_cases hnext : c.val + 1 < L
  · have hnval : (coordPeriodicNext c).val = c.val + 1 :=
      coordPeriodicNext_val_of_lt hnext
    have hpos : 0 < (coordPeriodicNext c).val := by omega
    have hpval : (coordPeriodicPrev (coordPeriodicNext c)).val =
        (coordPeriodicNext c).val - 1 :=
      coordPeriodicPrev_val_of_pos hpos
    omega
  · have hnval : (coordPeriodicNext c).val = 0 :=
      coordPeriodicNext_val_of_not_lt hnext
    have hpos : ¬ 0 < (coordPeriodicNext c).val := by omega
    have hpval : (coordPeriodicPrev (coordPeriodicNext c)).val = L - 1 :=
      coordPeriodicPrev_val_of_not_pos hpos
    omega

lemma coordPeriodicNext_eq_add_one {L : ℕ} [NeZero L] (a : Fin L) :
    coordPeriodicNext a = a + 1 := by
  cases L with
  | zero => exact (NeZero.ne 0) rfl |>.elim
  | succ N =>
    ext
    by_cases hnext : a.val + 1 < N + 1
    · rw [coordPeriodicNext_val_of_lt hnext, Fin.val_add]
      have hone : ((1 : Fin (N + 1)).val) = 1 := by
        rw [Fin.val_one']
        exact Nat.mod_eq_of_lt (by omega : 1 < N + 1)
      rw [hone]
      exact (Nat.mod_eq_of_lt hnext).symm
    · rw [coordPeriodicNext_val_of_not_lt hnext]
      have hlast : a.val + 1 = N + 1 := by omega
      simp [Fin.val_add, hlast]

lemma coordPeriodicPrev_eq_sub_one {L : ℕ} [NeZero L] (a : Fin L) :
    coordPeriodicPrev a = a - 1 := by
  cases L with
  | zero => exact (NeZero.ne 0) rfl |>.elim
  | succ N =>
    ext
    by_cases hpos : 0 < a.val
    · rw [coordPeriodicPrev_val_of_pos hpos]
      have hane : a ≠ 0 := by
        have hapos : 0 < a := by
          simpa [Fin.val_pos_iff] using hpos
        exact ne_of_gt hapos
      exact (Fin.val_sub_one_of_ne_zero hane).symm
    · rw [coordPeriodicPrev_val_of_not_pos hpos]
      have hazero : a = 0 := by
        ext
        exact Nat.eq_zero_of_not_pos hpos
      subst hazero
      simp [sub_eq_add_neg]

lemma coordPeriodicNext_zmod {L : ℕ} [NeZero L] (a : Fin L) :
    (ZMod.finEquiv L) (coordPeriodicNext a) = (ZMod.finEquiv L) a + 1 := by
  rw [coordPeriodicNext_eq_add_one]
  rw [map_add]
  simp

lemma coordPeriodicPrev_zmod {L : ℕ} [NeZero L] (a : Fin L) :
    (ZMod.finEquiv L) (coordPeriodicPrev a) = (ZMod.finEquiv L) a - 1 := by
  rw [coordPeriodicPrev_eq_sub_one]
  rw [map_sub]
  simp

lemma coordPeriodicNext_ne_prev_of_three_le {L : ℕ} (hL : 3 ≤ L)
    (a : Fin L) : coordPeriodicNext a ≠ coordPeriodicPrev a := by
  intro h
  have hnext : coordPeriodicNext (coordPeriodicNext a) = a := by
    rw [h]
    exact coordPeriodicNext_prev a
  exact coordPeriodicNext_next_ne_self hL a hnext

lemma coordPeriodicNext_injective {L : ℕ} :
    Function.Injective (@coordPeriodicNext L) := by
  intro a b h
  have hp := congrArg coordPeriodicPrev h
  simpa [coordPeriodicPrev_next] using hp

lemma eq_coordPeriodicPrev_of_coordPeriodicNext_eq {L : ℕ} {a b : Fin L}
    (h : coordPeriodicNext b = a) :
    b = coordPeriodicPrev a := by
  calc
    b = coordPeriodicPrev (coordPeriodicNext b) :=
      (coordPeriodicPrev_next b).symm
    _ = coordPeriodicPrev a := by rw [h]

lemma coordInPeriodicClosedTwoBlock_iff_center_eq_or_prev {L : ℕ}
    (a c : Fin L) :
    coordInPeriodicClosedTwoBlock a c ↔ c = a ∨ c = coordPeriodicPrev a := by
  unfold coordInPeriodicClosedTwoBlock coordPeriodicPrev
  by_cases hpos : 0 < a.val
  · constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inl h.symm
      · exact Or.inr (Fin.ext (by simp [hpos]; omega))
      · exact False.elim (by omega)
    · intro h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inl (by
          have hval := congrArg Fin.val h
          simp [hpos] at hval
          omega))
  · have hazero : a.val = 0 := Nat.eq_zero_of_not_pos hpos
    constructor
    · intro h
      rcases h with h | h | h
      · exact Or.inl h.symm
      · exact False.elim (by omega)
      · exact Or.inr (Fin.ext (by simp [hpos]; omega))
    · intro h
      rcases h with h | h
      · exact Or.inl h.symm
      · exact Or.inr (Or.inr ⟨by
          have hval := congrArg Fin.val h
          simp [hpos] at hval
          omega, hazero⟩)

noncomputable def coordPeriodicClosedTwoBlockCenterSet
    (L : ℕ) (a : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun c => coordInPeriodicClosedTwoBlock a c

lemma coordPeriodicClosedTwoBlockCenterSet_mem {L : ℕ} (a c : Fin L) :
    c ∈ coordPeriodicClosedTwoBlockCenterSet L a ↔
      coordInPeriodicClosedTwoBlock a c := by
  classical
  simp [coordPeriodicClosedTwoBlockCenterSet]

lemma coordPeriodicClosedTwoBlockCenterSet_eq_pair {L : ℕ} (a : Fin L) :
    coordPeriodicClosedTwoBlockCenterSet L a =
      {a, coordPeriodicPrev a} := by
  classical
  ext c
  rw [coordPeriodicClosedTwoBlockCenterSet_mem,
    coordInPeriodicClosedTwoBlock_iff_center_eq_or_prev]
  simp [eq_comm]

lemma coordPeriodicClosedTwoBlockCenterSet_card_eq_two {L : ℕ}
    (hL : 2 ≤ L) (a : Fin L) :
    (coordPeriodicClosedTwoBlockCenterSet L a).card = 2 := by
  classical
  rw [coordPeriodicClosedTwoBlockCenterSet_eq_pair]
  have hne : a ≠ coordPeriodicPrev a := (coordPeriodicPrev_ne_self hL a).symm
  simp [hne]

lemma coordInClosedTwoBlock_to_periodic {L : ℕ} {a c : Fin L}
    (h : coordInClosedTwoBlock a c) :
    coordInPeriodicClosedTwoBlock a c := by
  rcases h with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

lemma finCycleGraph_adj_periodicClosedTwoBlock_common {L : ℕ} {i j : Fin L}
    (h : (finCycleGraph L).Adj i j) :
    ∃ a : Fin L,
      coordInPeriodicClosedTwoBlock a i ∧ coordInPeriodicClosedTwoBlock a j := by
  rcases h with ⟨hne, hcases⟩
  rcases hcases with hpath | hwrap | hwrap
  · rcases pathGraph_adj_closedTwoBlock_common hpath with ⟨a, hai, haj⟩
    exact ⟨a, coordInClosedTwoBlock_to_periodic hai,
      coordInClosedTwoBlock_to_periodic haj⟩
  · refine ⟨i, Or.inl rfl, ?_⟩
    exact Or.inr (Or.inr ⟨hwrap.2, hwrap.1⟩)
  · refine ⟨j, ?_, Or.inl rfl⟩
    exact Or.inr (Or.inr ⟨hwrap.2, hwrap.1⟩)

def periodicCubeCoarseGraph (L : ℕ) : SimpleGraph (CubeCoord L) :=
  (finCycleGraph L □ finCycleGraph L) □ finCycleGraph L

def cubeCoordInPeriodicTwoByTwoByTwoStar {L : ℕ}
    (a c : CubeCoord L) : Prop :=
  coordInPeriodicClosedTwoBlock a.1.1 c.1.1 ∧
    coordInPeriodicClosedTwoBlock a.1.2 c.1.2 ∧
      coordInPeriodicClosedTwoBlock a.2 c.2

noncomputable def cubePeriodicStarSourceSet (L : ℕ) (c : CubeCoord L) :
    Finset (CubeCoord L) := by
  classical
  exact
    (coordPeriodicClosedTwoBlockSet L c.1.1 ×ˢ
      coordPeriodicClosedTwoBlockSet L c.1.2) ×ˢ
        coordPeriodicClosedTwoBlockSet L c.2

lemma cubePeriodicStarSourceSet_mem {L : ℕ} (a c : CubeCoord L) :
    a ∈ cubePeriodicStarSourceSet L c ↔
      cubeCoordInPeriodicTwoByTwoByTwoStar a c := by
  classical
  simp [cubePeriodicStarSourceSet, cubeCoordInPeriodicTwoByTwoByTwoStar,
    coordPeriodicClosedTwoBlockSet_mem, and_assoc]

lemma cubePeriodicStarSourceSet_card_eq_eight {L : ℕ}
    (hL : 2 ≤ L) (c : CubeCoord L) :
    (cubePeriodicStarSourceSet L c).card = 8 := by
  classical
  rw [cubePeriodicStarSourceSet]
  rw [Finset.card_product, Finset.card_product]
  simp [coordPeriodicClosedTwoBlockSet_card_eq_two hL]

noncomputable def cubePeriodicStarCenterSet (L : ℕ) (a : CubeCoord L) :
    Finset (CubeCoord L) := by
  classical
  exact
    (coordPeriodicClosedTwoBlockCenterSet L a.1.1 ×ˢ
      coordPeriodicClosedTwoBlockCenterSet L a.1.2) ×ˢ
        coordPeriodicClosedTwoBlockCenterSet L a.2

lemma cubePeriodicStarCenterSet_mem {L : ℕ} (a c : CubeCoord L) :
    c ∈ cubePeriodicStarCenterSet L a ↔
      cubeCoordInPeriodicTwoByTwoByTwoStar a c := by
  classical
  simp [cubePeriodicStarCenterSet, cubeCoordInPeriodicTwoByTwoByTwoStar,
    coordPeriodicClosedTwoBlockCenterSet_mem, and_assoc]

lemma cubePeriodicStarCenterSet_card_eq_eight {L : ℕ}
    (hL : 2 ≤ L) (a : CubeCoord L) :
    (cubePeriodicStarCenterSet L a).card = 8 := by
  classical
  rw [cubePeriodicStarCenterSet]
  rw [Finset.card_product, Finset.card_product]
  simp [coordPeriodicClosedTwoBlockCenterSet_card_eq_two hL]

lemma periodicCubeCoarseGraph_connected (L : ℕ) (hL : 4 ≤ L) :
    (periodicCubeCoarseGraph L).Connected := by
  have hc : (finCycleGraph L).Connected := finCycleGraph_connected_of_four_le L hL
  exact (hc.boxProd hc).boxProd hc

lemma periodicCubeCoarseGraph_adj_star_common {L : ℕ} {c d : CubeCoord L}
    (h : (periodicCubeCoarseGraph L).Adj c d) :
    ∃ a : CubeCoord L,
      cubeCoordInPeriodicTwoByTwoByTwoStar a c ∧
        cubeCoordInPeriodicTwoByTwoByTwoStar a d := by
  rw [periodicCubeCoarseGraph, SimpleGraph.boxProd_adj] at h
  rcases h with hxy_z | hz_xy
  · rcases hxy_z with ⟨hxy, hz⟩
    rw [SimpleGraph.boxProd_adj] at hxy
    rcases hxy with hxy | hxy
    · rcases hxy with ⟨hx, hy⟩
      rcases finCycleGraph_adj_periodicClosedTwoBlock_common hx with ⟨ax, haxc, haxd⟩
      refine ⟨((ax, c.1.2), c.2), ?_⟩
      constructor
      · exact ⟨haxc, Or.inl rfl, Or.inl rfl⟩
      · refine ⟨haxd, ?_, ?_⟩
        · rw [← hy]
          exact Or.inl rfl
        · rw [← hz]
          exact Or.inl rfl
    · rcases hxy with ⟨hy, hx⟩
      rcases finCycleGraph_adj_periodicClosedTwoBlock_common hy with ⟨ay, hayc, hayd⟩
      refine ⟨((c.1.1, ay), c.2), ?_⟩
      constructor
      · exact ⟨Or.inl rfl, hayc, Or.inl rfl⟩
      · refine ⟨?_, hayd, ?_⟩
        · rw [← hx]
          exact Or.inl rfl
        · rw [← hz]
          exact Or.inl rfl
  · rcases hz_xy with ⟨hz, hxy⟩
    rcases finCycleGraph_adj_periodicClosedTwoBlock_common hz with ⟨az, hazc, hazd⟩
    have hx : c.1.1 = d.1.1 := congrArg Prod.fst hxy
    have hy : c.1.2 = d.1.2 := congrArg Prod.snd hxy
    refine ⟨((c.1.1, c.1.2), az), ?_⟩
    constructor
    · exact ⟨Or.inl rfl, Or.inl rfl, hazc⟩
    · refine ⟨?_, ?_, hazd⟩
      · rw [← hx]
        exact Or.inl rfl
      · rw [← hy]
        exact Or.inl rfl

def sigmaPeriodicCoarseGraph4 (L : ℕ) : SimpleGraph (SigmaCoord4 L) :=
  periodicCubeCoarseGraph L □ finCycleGraph L

def sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar {L : ℕ}
    (a c : SigmaCoord4 L) : Prop :=
  cubeCoordInPeriodicTwoByTwoByTwoStar a.1 c.1 ∧
    coordInPeriodicClosedTwoBlock a.2 c.2

noncomputable def sigmaPeriodicStarSourceSet4
    (L : ℕ) (c : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact cubePeriodicStarSourceSet L c.1 ×ˢ
    coordPeriodicClosedTwoBlockSet L c.2

lemma sigmaPeriodicStarSourceSet4_mem {L : ℕ}
    (a c : SigmaCoord4 L) :
    a ∈ sigmaPeriodicStarSourceSet4 L c ↔
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a c := by
  classical
  simp [sigmaPeriodicStarSourceSet4,
    sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar,
    cubePeriodicStarSourceSet_mem,
    coordPeriodicClosedTwoBlockSet_mem]

lemma sigmaPeriodicStarSourceSet4_card_eq_sixteen {L : ℕ}
    (hL : 2 ≤ L) (c : SigmaCoord4 L) :
    (sigmaPeriodicStarSourceSet4 L c).card = 16 := by
  classical
  rw [sigmaPeriodicStarSourceSet4]
  rw [Finset.card_product]
  simp [cubePeriodicStarSourceSet_card_eq_eight hL,
    coordPeriodicClosedTwoBlockSet_card_eq_two hL]

noncomputable def sigmaPeriodicStarCenterSet4
    (L : ℕ) (a : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact cubePeriodicStarCenterSet L a.1 ×ˢ
    coordPeriodicClosedTwoBlockCenterSet L a.2

lemma sigmaPeriodicStarCenterSet4_mem {L : ℕ}
    (a c : SigmaCoord4 L) :
    c ∈ sigmaPeriodicStarCenterSet4 L a ↔
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a c := by
  classical
  simp [sigmaPeriodicStarCenterSet4,
    sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar,
    cubePeriodicStarCenterSet_mem,
    coordPeriodicClosedTwoBlockCenterSet_mem]

lemma sigmaPeriodicStarCenterSet4_card_eq_sixteen {L : ℕ}
    (hL : 2 ≤ L) (a : SigmaCoord4 L) :
    (sigmaPeriodicStarCenterSet4 L a).card = 16 := by
  classical
  rw [sigmaPeriodicStarCenterSet4]
  rw [Finset.card_product]
  simp [cubePeriodicStarCenterSet_card_eq_eight hL,
    coordPeriodicClosedTwoBlockCenterSet_card_eq_two hL]

lemma sigmaPeriodicCoarseGraph4_connected (L : ℕ) (hL : 4 ≤ L) :
    (sigmaPeriodicCoarseGraph4 L).Connected := by
  have hc : (periodicCubeCoarseGraph L).Connected :=
    periodicCubeCoarseGraph_connected L hL
  have ht : (finCycleGraph L).Connected := finCycleGraph_connected_of_four_le L hL
  exact hc.boxProd ht

lemma sigmaPeriodicCoarseGraph4_adj_star_common {L : ℕ} {c d : SigmaCoord4 L}
    (h : (sigmaPeriodicCoarseGraph4 L).Adj c d) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a c ∧
        sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a d := by
  rw [sigmaPeriodicCoarseGraph4, SimpleGraph.boxProd_adj] at h
  rcases h with hcube_w | hw_cube
  · rcases hcube_w with ⟨hcube, hw⟩
    rcases periodicCubeCoarseGraph_adj_star_common hcube with ⟨a, hac, had⟩
    refine ⟨(a, c.2), ?_⟩
    constructor
    · exact ⟨hac, Or.inl rfl⟩
    · refine ⟨had, ?_⟩
      rw [← hw]
      exact Or.inl rfl
  · rcases hw_cube with ⟨hw, hcube⟩
    rcases finCycleGraph_adj_periodicClosedTwoBlock_common hw with ⟨a, hac, had⟩
    refine ⟨(c.1, a), ?_⟩
    constructor
    · exact ⟨by
        rw [cubeCoordInPeriodicTwoByTwoByTwoStar]
        exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩, hac⟩
    · refine ⟨?_, had⟩
      rw [← hcube]
      rw [cubeCoordInPeriodicTwoByTwoByTwoStar]
      exact ⟨Or.inl rfl, Or.inl rfl, Or.inl rfl⟩

abbrev SigmaPeriodicFineEdge4 (L : ℕ) := SigmaCoord4 L × Fin 4

noncomputable def sigmaPeriodicFineEdgeContainingCenters4
    (L : ℕ) (e : SigmaPeriodicFineEdge4 L) :
    Finset (SigmaCoord4 L) :=
  sigmaPeriodicStarCenterSet4 L e.1

lemma sigmaPeriodicFineEdgeContainingCenters4_mem {L : ℕ}
    (e : SigmaPeriodicFineEdge4 L) (c : SigmaCoord4 L) :
    c ∈ sigmaPeriodicFineEdgeContainingCenters4 L e ↔
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar e.1 c := by
  simp [sigmaPeriodicFineEdgeContainingCenters4,
    sigmaPeriodicStarCenterSet4_mem]

lemma sigmaPeriodicFineEdgeContainingCenters4_card_eq_sixteen {L : ℕ}
    (hL : 2 ≤ L) (e : SigmaPeriodicFineEdge4 L) :
    (sigmaPeriodicFineEdgeContainingCenters4 L e).card = 16 :=
  sigmaPeriodicStarCenterSet4_card_eq_sixteen hL e.1

noncomputable def sigmaPeriodicBlockStarSupportProduct4
    (L : ℕ) (c : SigmaCoord4 L) :
    Finset (SigmaPeriodicFineEdge4 L) := by
  classical
  exact sigmaPeriodicStarSourceSet4 L c ×ˢ Finset.univ

lemma sigmaPeriodicBlockStarSupportProduct4_mem {L : ℕ}
    (e : SigmaPeriodicFineEdge4 L) (c : SigmaCoord4 L) :
    e ∈ sigmaPeriodicBlockStarSupportProduct4 L c ↔
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar e.1 c := by
  classical
  simp [sigmaPeriodicBlockStarSupportProduct4,
    sigmaPeriodicStarSourceSet4_mem]

lemma sigmaPeriodicBlockStarSupportProduct4_card_eq_sixty_four {L : ℕ}
    (hL : 2 ≤ L) (c : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupportProduct4 L c).card = 64 := by
  classical
  rw [sigmaPeriodicBlockStarSupportProduct4]
  rw [Finset.card_product]
  simp [sigmaPeriodicStarSourceSet4_card_eq_sixteen hL]

noncomputable def sigmaPeriodicBlockStarSupport4 (L : ℕ)
    (c : SigmaCoord4 L) : Finset (SigmaPeriodicFineEdge4 L) := by
  classical
  exact Finset.univ.filter fun e =>
    sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar e.1 c

lemma sigmaPeriodicBlockStarSupport4_eq_product (L : ℕ)
    (c : SigmaCoord4 L) :
    sigmaPeriodicBlockStarSupport4 L c =
      sigmaPeriodicBlockStarSupportProduct4 L c := by
  classical
  ext e
  rw [sigmaPeriodicBlockStarSupportProduct4_mem]
  simp [sigmaPeriodicBlockStarSupport4]

lemma sigmaPeriodicBlockStarSupport4_card_eq_sixty_four {L : ℕ}
    (hL : 2 ≤ L) (c : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupport4 L c).card = 64 := by
  rw [sigmaPeriodicBlockStarSupport4_eq_product]
  exact sigmaPeriodicBlockStarSupportProduct4_card_eq_sixty_four hL c

noncomputable def coordPeriodicClosedTwoBlockOverlapCard
    {L : ℕ} (a b : Fin L) : ℕ :=
  (coordPeriodicClosedTwoBlockSet L a ∩
    coordPeriodicClosedTwoBlockSet L b).card

lemma coordPeriodicClosedTwoBlockOverlapCard_symm {L : ℕ}
    (a b : Fin L) :
    coordPeriodicClosedTwoBlockOverlapCard a b =
      coordPeriodicClosedTwoBlockOverlapCard b a := by
  classical
  unfold coordPeriodicClosedTwoBlockOverlapCard
  rw [Finset.inter_comm]

lemma coordPeriodicClosedTwoBlockOverlapCard_self {L : ℕ}
    (hL : 2 ≤ L) (c : Fin L) :
    coordPeriodicClosedTwoBlockOverlapCard c c = 2 := by
  classical
  unfold coordPeriodicClosedTwoBlockOverlapCard
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  have hne : c ≠ coordPeriodicNext c := (coordPeriodicNext_ne_self hL c).symm
  simp [hne]

lemma coordPeriodicClosedTwoBlockOverlapCard_next {L : ℕ}
    (hL : 3 ≤ L) (c : Fin L) :
    coordPeriodicClosedTwoBlockOverlapCard c (coordPeriodicNext c) = 1 := by
  classical
  unfold coordPeriodicClosedTwoBlockOverlapCard
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  have hne2 : c ≠ coordPeriodicNext (coordPeriodicNext c) :=
    (coordPeriodicNext_next_ne_self hL c).symm
  have hne3 : coordPeriodicNext c ≠ coordPeriodicNext (coordPeriodicNext c) :=
    (coordPeriodicNext_ne_self (le_trans (by norm_num : 2 ≤ 3) hL)
      (coordPeriodicNext c)).symm
  simp [hne2, hne3]

lemma coordPeriodicClosedTwoBlockOverlapCard_prev {L : ℕ}
    (hL : 3 ≤ L) (c : Fin L) :
    coordPeriodicClosedTwoBlockOverlapCard c (coordPeriodicPrev c) = 1 := by
  calc
    coordPeriodicClosedTwoBlockOverlapCard c (coordPeriodicPrev c) =
        coordPeriodicClosedTwoBlockOverlapCard (coordPeriodicPrev c) c := by
      rw [coordPeriodicClosedTwoBlockOverlapCard_symm]
    _ = coordPeriodicClosedTwoBlockOverlapCard
          (coordPeriodicPrev c) (coordPeriodicNext (coordPeriodicPrev c)) := by
      rw [coordPeriodicNext_prev c]
    _ = 1 := coordPeriodicClosedTwoBlockOverlapCard_next hL (coordPeriodicPrev c)

lemma coordPeriodicClosedTwoBlockOverlapCard_eq_zero_of_not_neighbor {L : ℕ}
    {a b : Fin L}
    (hba : b ≠ a)
    (hbn : b ≠ coordPeriodicNext a)
    (hbp : b ≠ coordPeriodicPrev a) :
    coordPeriodicClosedTwoBlockOverlapCard a b = 0 := by
  classical
  unfold coordPeriodicClosedTwoBlockOverlapCard
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  rw [coordPeriodicClosedTwoBlockSet_eq_pair]
  rw [Finset.card_eq_zero]
  ext x
  constructor
  · intro hx
    have hxa : x = a ∨ x = coordPeriodicNext a := by
      simpa using (Finset.mem_inter.mp hx).1
    have hxb : x = b ∨ x = coordPeriodicNext b := by
      simpa using (Finset.mem_inter.mp hx).2
    rcases hxa with hxa | hxa <;> rcases hxb with hxb | hxb
    · exact False.elim (hba (hxb.symm.trans hxa))
    · have hbprev : b = coordPeriodicPrev a :=
        eq_coordPeriodicPrev_of_coordPeriodicNext_eq (hxb.symm.trans hxa)
      exact False.elim (hbp hbprev)
    · exact False.elim (hbn (hxb.symm.trans hxa))
    · have hbnext : coordPeriodicNext b = coordPeriodicNext a :=
        hxb.symm.trans hxa
      have hbeq : b = a := coordPeriodicNext_injective hbnext
      exact False.elim (hba hbeq)
  · intro hx
    simp at hx

def coordPeriodicClosedTwoBlockConvolutionKernel {L : ℕ}
    (a b : Fin L) : ℕ :=
  if b = a then 2 else if b = coordPeriodicNext a then 1
    else if b = coordPeriodicPrev a then 1 else 0

lemma coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel
    {L : ℕ} (hL : 3 ≤ L) (a b : Fin L) :
    coordPeriodicClosedTwoBlockOverlapCard a b =
      coordPeriodicClosedTwoBlockConvolutionKernel a b := by
  classical
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 3) hL
  unfold coordPeriodicClosedTwoBlockConvolutionKernel
  by_cases hba : b = a
  · subst b
    simp [coordPeriodicClosedTwoBlockOverlapCard_self hL2]
  · by_cases hbn : b = coordPeriodicNext a
    · subst b
      simp [hba, coordPeriodicClosedTwoBlockOverlapCard_next hL]
    · by_cases hbp : b = coordPeriodicPrev a
      · subst b
        simp [hba, hbn, coordPeriodicClosedTwoBlockOverlapCard_prev hL]
      · rw [coordPeriodicClosedTwoBlockOverlapCard_eq_zero_of_not_neighbor hba hbn hbp]
        simp [hba, hbn, hbp]

noncomputable def coordPeriodicConvolutionSupport
    (L : ℕ) (a : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun b =>
    coordPeriodicClosedTwoBlockConvolutionKernel a b ≠ 0

lemma coordPeriodicConvolutionSupport_subset_triple
    (L : ℕ) (a : Fin L) :
    coordPeriodicConvolutionSupport L a ⊆
      ({a, coordPeriodicNext a, coordPeriodicPrev a} : Finset (Fin L)) := by
  classical
  intro b hb
  have hk : coordPeriodicClosedTwoBlockConvolutionKernel a b ≠ 0 := by
    simpa [coordPeriodicConvolutionSupport] using (Finset.mem_filter.mp hb).2
  unfold coordPeriodicClosedTwoBlockConvolutionKernel at hk
  by_cases hba : b = a
  · simp [hba]
  · by_cases hbn : b = coordPeriodicNext a
    · simp [hbn]
    · by_cases hbp : b = coordPeriodicPrev a
      · simp [hbp]
      · simp [hba, hbn, hbp] at hk

lemma coordPeriodicConvolutionSupport_card_le_three
    (L : ℕ) (a : Fin L) :
    (coordPeriodicConvolutionSupport L a).card ≤ 3 := by
  classical
  have hsub := coordPeriodicConvolutionSupport_subset_triple L a
  have hcard := Finset.card_le_card hsub
  have htriple :
      ({a, coordPeriodicNext a, coordPeriodicPrev a} : Finset (Fin L)).card ≤ 3 := by
    have h1 := Finset.card_insert_le a
      ({coordPeriodicNext a, coordPeriodicPrev a} : Finset (Fin L))
    have h2 := Finset.card_insert_le (coordPeriodicNext a)
      ({coordPeriodicPrev a} : Finset (Fin L))
    simp at h2
    omega
  exact hcard.trans htriple

lemma coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply {L : ℕ}
    (hL : 3 ≤ L) (a : Fin L) (φ : Fin L → ℝ) :
    (∑ b, (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) * φ b) =
      2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
  classical
  let S : Finset (Fin L) := {a, coordPeriodicNext a, coordPeriodicPrev a}
  have hsubset : S ⊆ (Finset.univ : Finset (Fin L)) :=
    fun b _ => Finset.mem_univ b
  have hzero : ∀ b ∈ (Finset.univ : Finset (Fin L)), b ∉ S →
      (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) * φ b = 0 := by
    intro b _ hb
    have hba : b ≠ a := by
      intro h
      exact hb (by simp [S, h])
    have hbn : b ≠ coordPeriodicNext a := by
      intro h
      exact hb (by simp [S, h])
    have hbp : b ≠ coordPeriodicPrev a := by
      intro h
      exact hb (by simp [S, h])
    simp [coordPeriodicClosedTwoBlockConvolutionKernel, hba, hbn, hbp]
  calc
    (∑ b, (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) * φ b) =
        S.sum
          (fun b => (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) *
            φ b) := by
      exact (Finset.sum_subset hsubset hzero).symm
    _ = 2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
      have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 3) hL
      have hna : coordPeriodicNext a ≠ a := coordPeriodicNext_ne_self hL2 a
      have hpa : coordPeriodicPrev a ≠ a := by
        intro h
        have hn := coordPeriodicNext_prev a
        rw [h] at hn
        exact hna hn
      have hnp : coordPeriodicNext a ≠ coordPeriodicPrev a :=
        coordPeriodicNext_ne_prev_of_three_le hL a
      change ({a, coordPeriodicNext a, coordPeriodicPrev a} :
          Finset (Fin L)).sum
            (fun b => (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) *
              φ b) =
        2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a)
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_singleton]
          simp [coordPeriodicClosedTwoBlockConvolutionKernel, hna, hpa]
          ring
        · simp [hnp]
      · intro ha
        simp only [Finset.mem_singleton, Finset.mem_insert] at ha
        rcases ha with ha | ha
        · exact hna ha.symm
        · exact hpa ha.symm

lemma coordPeriodicClosedTwoBlockConvolutionKernel_sum {L : ℕ}
    (hL : 3 ≤ L) (a : Fin L) :
    (∑ b, (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ)) = 4 := by
  have h := coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply hL a
    (fun _ : Fin L => (1 : ℝ))
  norm_num at h
  exact h

lemma fourfold_univ_sum_product
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℝ) (g : B → ℝ) (h : C → ℝ) (k : D → ℝ) :
    ((((∑ x, f x) * (∑ y, g y)) * (∑ z, h z)) * (∑ t, k t)) =
      ∑ p : (((A × B) × C) × D),
        (((f p.1.1.1 * g p.1.1.2) * h p.1.2) * k p.2) := by
  classical
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_mul]

lemma fourfold_univ_sum_product_complex
    {A B C D : Type*} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → ℂ) (g : B → ℂ) (h : C → ℂ) (k : D → ℂ) :
    ((((∑ x, f x) * (∑ y, g y)) * (∑ z, h z)) * (∑ t, k t)) =
      ∑ p : (((A × B) × C) × D),
        (((f p.1.1.1 * g p.1.1.2) * h p.1.2) * k p.2) := by
  classical
  simp_rw [Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  ring_nf
  refine Finset.sum_congr rfl ?_
  intro x _
  refine Finset.sum_congr rfl ?_
  intro y _
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl ?_
  intro z _
  rw [Finset.sum_mul]

lemma cubePeriodicStarSourceSet_inter_card {L : ℕ}
    (c d : CubeCoord L) :
    (cubePeriodicStarSourceSet L c ∩
        cubePeriodicStarSourceSet L d).card =
      (coordPeriodicClosedTwoBlockOverlapCard c.1.1 d.1.1 *
        coordPeriodicClosedTwoBlockOverlapCard c.1.2 d.1.2) *
          coordPeriodicClosedTwoBlockOverlapCard c.2 d.2 := by
  classical
  rw [cubePeriodicStarSourceSet, cubePeriodicStarSourceSet]
  rw [Finset.product_inter_product]
  rw [Finset.product_inter_product]
  rw [Finset.card_product, Finset.card_product]
  rfl

lemma sigmaPeriodicStarSourceSet4_inter_card {L : ℕ}
    (c d : SigmaCoord4 L) :
    (sigmaPeriodicStarSourceSet4 L c ∩
        sigmaPeriodicStarSourceSet4 L d).card =
      ((coordPeriodicClosedTwoBlockOverlapCard c.1.1.1 d.1.1.1 *
        coordPeriodicClosedTwoBlockOverlapCard c.1.1.2 d.1.1.2) *
          coordPeriodicClosedTwoBlockOverlapCard c.1.2 d.1.2) *
            coordPeriodicClosedTwoBlockOverlapCard c.2 d.2 := by
  classical
  rw [sigmaPeriodicStarSourceSet4, sigmaPeriodicStarSourceSet4]
  rw [Finset.product_inter_product]
  rw [Finset.card_product]
  rw [cubePeriodicStarSourceSet_inter_card]
  rfl

lemma sigmaPeriodicBlockStarSupportProduct4_inter_card {L : ℕ}
    (c d : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupportProduct4 L c ∩
        sigmaPeriodicBlockStarSupportProduct4 L d).card =
      (sigmaPeriodicStarSourceSet4 L c ∩
        sigmaPeriodicStarSourceSet4 L d).card * 4 := by
  classical
  rw [sigmaPeriodicBlockStarSupportProduct4,
    sigmaPeriodicBlockStarSupportProduct4]
  rw [Finset.product_inter_product]
  rw [Finset.card_product]
  simp

lemma sigmaPeriodicBlockStarSupport4_inter_card {L : ℕ}
    (c d : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupport4 L c ∩
        sigmaPeriodicBlockStarSupport4 L d).card =
      (((coordPeriodicClosedTwoBlockOverlapCard c.1.1.1 d.1.1.1 *
        coordPeriodicClosedTwoBlockOverlapCard c.1.1.2 d.1.1.2) *
          coordPeriodicClosedTwoBlockOverlapCard c.1.2 d.1.2) *
            coordPeriodicClosedTwoBlockOverlapCard c.2 d.2) * 4 := by
  classical
  rw [sigmaPeriodicBlockStarSupport4_eq_product,
    sigmaPeriodicBlockStarSupport4_eq_product]
  rw [sigmaPeriodicBlockStarSupportProduct4_inter_card]
  rw [sigmaPeriodicStarSourceSet4_inter_card]

def sigmaPeriodicTensorConvolutionKernel4 {L : ℕ}
    (i j : SigmaCoord4 L) : ℕ :=
  ((coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.1 j.1.1.1 *
    coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.2 j.1.1.2) *
      coordPeriodicClosedTwoBlockConvolutionKernel i.1.2 j.1.2) *
        coordPeriodicClosedTwoBlockConvolutionKernel i.2 j.2

noncomputable def sigmaPeriodicTensorConvolutionSupport4
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact Finset.univ.filter fun j =>
    sigmaPeriodicTensorConvolutionKernel4 i j ≠ 0

lemma sigmaPeriodicTensorConvolutionKernel4_eq_zero_of_not_mem_support
    (L : ℕ) (i j : SigmaCoord4 L)
    (hj : j ∉ sigmaPeriodicTensorConvolutionSupport4 L i) :
    sigmaPeriodicTensorConvolutionKernel4 i j = 0 := by
  classical
  by_contra hne
  exact hj (by simp [sigmaPeriodicTensorConvolutionSupport4, hne])

lemma sigmaPeriodicTensorConvolutionSupport4_subset_product
    (L : ℕ) (i : SigmaCoord4 L) :
    sigmaPeriodicTensorConvolutionSupport4 L i ⊆
      ((((coordPeriodicConvolutionSupport L i.1.1.1 ×ˢ
          coordPeriodicConvolutionSupport L i.1.1.2) ×ˢ
            coordPeriodicConvolutionSupport L i.1.2) ×ˢ
              coordPeriodicConvolutionSupport L i.2) :
        Finset (SigmaCoord4 L)) := by
  classical
  intro j hj
  have hk : sigmaPeriodicTensorConvolutionKernel4 i j ≠ 0 := by
    simpa [sigmaPeriodicTensorConvolutionSupport4] using
      (Finset.mem_filter.mp hj).2
  have hx :
      coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.1 j.1.1.1 ≠ 0 := by
    intro h
    exact hk (by simp [sigmaPeriodicTensorConvolutionKernel4, h])
  have hy :
      coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.2 j.1.1.2 ≠ 0 := by
    intro h
    exact hk (by simp [sigmaPeriodicTensorConvolutionKernel4, h])
  have hz :
      coordPeriodicClosedTwoBlockConvolutionKernel i.1.2 j.1.2 ≠ 0 := by
    intro h
    exact hk (by simp [sigmaPeriodicTensorConvolutionKernel4, h])
  have ht :
      coordPeriodicClosedTwoBlockConvolutionKernel i.2 j.2 ≠ 0 := by
    intro h
    exact hk (by simp [sigmaPeriodicTensorConvolutionKernel4, h])
  simp [coordPeriodicConvolutionSupport, hx, hy, hz, ht]

lemma sigmaPeriodicTensorConvolutionSupport4_card_le_eighty_one
    (L : ℕ) (i : SigmaCoord4 L) :
    (sigmaPeriodicTensorConvolutionSupport4 L i).card ≤ 81 := by
  classical
  let sx := coordPeriodicConvolutionSupport L i.1.1.1
  let sy := coordPeriodicConvolutionSupport L i.1.1.2
  let sz := coordPeriodicConvolutionSupport L i.1.2
  let st := coordPeriodicConvolutionSupport L i.2
  have hsub :
      sigmaPeriodicTensorConvolutionSupport4 L i ⊆ (((sx ×ˢ sy) ×ˢ sz) ×ˢ st) := by
    simpa [sx, sy, sz, st] using
      sigmaPeriodicTensorConvolutionSupport4_subset_product L i
  have hcard := Finset.card_le_card hsub
  have hx : sx.card ≤ 3 := by
    simpa [sx] using coordPeriodicConvolutionSupport_card_le_three L i.1.1.1
  have hy : sy.card ≤ 3 := by
    simpa [sy] using coordPeriodicConvolutionSupport_card_le_three L i.1.1.2
  have hz : sz.card ≤ 3 := by
    simpa [sz] using coordPeriodicConvolutionSupport_card_le_three L i.1.2
  have ht : st.card ≤ 3 := by
    simpa [st] using coordPeriodicConvolutionSupport_card_le_three L i.2
  have hxy : sx.card * sy.card ≤ 3 * 3 := Nat.mul_le_mul hx hy
  have hxyz : (sx.card * sy.card) * sz.card ≤ (3 * 3) * 3 :=
    Nat.mul_le_mul hxy hz
  have hxyzt : ((sx.card * sy.card) * sz.card) * st.card ≤
      ((3 * 3) * 3) * 3 :=
    Nat.mul_le_mul hxyz ht
  have hprod : (((sx ×ˢ sy) ×ˢ sz) ×ˢ st).card ≤ 81 := by
    rw [Finset.card_product, Finset.card_product, Finset.card_product]
    norm_num at hxyzt ⊢
    exact hxyzt
  exact hcard.trans hprod

lemma sigmaPeriodicBlockStarSupport4_inter_card_eq_tensor_convolutionKernel
    {L : ℕ} (hL : 3 ≤ L) (i j : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupport4 L i ∩
        sigmaPeriodicBlockStarSupport4 L j).card =
      sigmaPeriodicTensorConvolutionKernel4 i j * 4 := by
  rw [sigmaPeriodicBlockStarSupport4_inter_card]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL
    i.1.1.1 j.1.1.1]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL
    i.1.1.2 j.1.1.2]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL
    i.1.2 j.1.2]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL
    i.2 j.2]
  rfl

lemma sigmaPeriodicBlockAveragingMatrixFromSupports_apply {L : ℕ}
    (hL : 2 ≤ L) (c : SigmaCoord4 L) (e : SigmaPeriodicFineEdge4 L) :
    blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L) c e =
      if e ∈ sigmaPeriodicBlockStarSupport4 L c then (64 : ℝ)⁻¹ else 0 := by
  classical
  by_cases he : e ∈ sigmaPeriodicBlockStarSupport4 L c
  · simp [blockAveragingMatrixFromSupports, he,
      sigmaPeriodicBlockStarSupport4_card_eq_sixty_four hL c]
  · simp [blockAveragingMatrixFromSupports, he]

lemma sigmaPeriodicCoarseOverlapMatrix_eq_inter_card {L : ℕ}
    (hL : 2 ≤ L) (i j : SigmaCoord4 L) :
    coarseOverlapMatrix
        (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L)) i j =
      (((sigmaPeriodicBlockStarSupport4 L i ∩
          sigmaPeriodicBlockStarSupport4 L j).card : ℝ) *
        (64 : ℝ)⁻¹ * (64 : ℝ)⁻¹) := by
  rw [coarseOverlapMatrix_fromSupports_apply_eq_inter_card]
  rw [sigmaPeriodicBlockStarSupport4_card_eq_sixty_four hL i,
    sigmaPeriodicBlockStarSupport4_card_eq_sixty_four hL j]
  norm_num

lemma sigmaPeriodicCoarseOverlapMatrix_eq_coord_overlap_card {L : ℕ}
    (hL : 2 ≤ L) (i j : SigmaCoord4 L) :
    coarseOverlapMatrix
        (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L)) i j =
      (((((coordPeriodicClosedTwoBlockOverlapCard i.1.1.1 j.1.1.1 *
        coordPeriodicClosedTwoBlockOverlapCard i.1.1.2 j.1.1.2) *
          coordPeriodicClosedTwoBlockOverlapCard i.1.2 j.1.2) *
            coordPeriodicClosedTwoBlockOverlapCard i.2 j.2) * 4 : ℕ) : ℝ) *
        (64 : ℝ)⁻¹ * (64 : ℝ)⁻¹ := by
  rw [sigmaPeriodicCoarseOverlapMatrix_eq_inter_card hL]
  rw [sigmaPeriodicBlockStarSupport4_inter_card]

lemma sigmaPeriodicBlockStarSupport4_nonempty (L : ℕ) (c : SigmaCoord4 L) :
    (sigmaPeriodicBlockStarSupport4 L c).Nonempty := by
  refine ⟨(c, 0), ?_⟩
  simp [sigmaPeriodicBlockStarSupport4,
    sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar,
    cubeCoordInPeriodicTwoByTwoByTwoStar,
    coordInPeriodicClosedTwoBlock]

lemma sigmaPeriodicFineEdgeContainingCenters4_mem_support_iff {L : ℕ}
    (e : SigmaPeriodicFineEdge4 L) (c : SigmaCoord4 L) :
    c ∈ sigmaPeriodicFineEdgeContainingCenters4 L e ↔
      e ∈ sigmaPeriodicBlockStarSupport4 L c := by
  rw [sigmaPeriodicFineEdgeContainingCenters4_mem]
  simp [sigmaPeriodicBlockStarSupport4]

lemma sigmaPeriodicBlockAveragingMatrixFromSupports_column_sum {L : ℕ}
    (hL : 2 ≤ L) (e : SigmaPeriodicFineEdge4 L) :
    ∑ c, blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L) c e =
      (1 / 4 : ℝ) := by
  classical
  let C := sigmaPeriodicFineEdgeContainingCenters4 L e
  calc
    ∑ c, blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L) c e =
        ∑ c, if c ∈ C then (64 : ℝ)⁻¹ else 0 := by
      refine Finset.sum_congr rfl ?_
      intro c _
      rw [sigmaPeriodicBlockAveragingMatrixFromSupports_apply hL]
      by_cases hc : c ∈ C
      · have he : e ∈ sigmaPeriodicBlockStarSupport4 L c := by
          simpa [C] using
            (sigmaPeriodicFineEdgeContainingCenters4_mem_support_iff e c).1 hc
        simp [hc, he]
      · have he : e ∉ sigmaPeriodicBlockStarSupport4 L c := by
          intro hsupport
          exact hc (by
            simpa [C] using
              (sigmaPeriodicFineEdgeContainingCenters4_mem_support_iff e c).2 hsupport)
        simp [hc, he]
    _ = C.sum (fun _ => (64 : ℝ)⁻¹) := by
      rw [Finset.sum_ite_mem_eq]
    _ = (1 / 4 : ℝ) := by
      simp [C, sigmaPeriodicFineEdgeContainingCenters4_card_eq_sixteen hL,
        Finset.sum_const, nsmul_eq_mul]
      norm_num

lemma sigmaPeriodicCoarseOverlapMatrix_blockDegree_eq_one_four {L : ℕ}
    (hL : 2 ≤ L) (i : SigmaCoord4 L) :
    blockDegree
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L))) i =
      (1 / 4 : ℝ) := by
  classical
  let M := blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L)
  have hrow :
      ∑ e, M i e = 1 :=
    blockAveragingMatrixFromSupports_rowStochastic
      (sigmaPeriodicBlockStarSupport4 L)
      (sigmaPeriodicBlockStarSupport4_nonempty L) i
  calc
    blockDegree
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L))) i =
        ∑ e, M i e * ∑ j, M j e := by
      simpa [M] using blockDegree_coarseOverlapMatrix_apply M i
    _ = ∑ e, M i e * (1 / 4 : ℝ) := by
      refine Finset.sum_congr rfl ?_
      intro e _
      rw [sigmaPeriodicBlockAveragingMatrixFromSupports_column_sum hL e]
    _ = (∑ e, M i e) * (1 / 4 : ℝ) := by
      rw [Finset.sum_mul]
    _ = (1 / 4 : ℝ) := by
      rw [hrow]
      ring

lemma sigmaPeriodicRandomWalkLaplacian_fromSupports_apply {L : ℕ}
    (hL : 2 ≤ L) (i j : SigmaCoord4 L) :
    randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L))) i j =
      (if i = j then 1 else 0) -
        4 * coarseOverlapMatrix
          (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L)) i j := by
  rw [randomWalkLaplacian_apply]
  rw [sigmaPeriodicCoarseOverlapMatrix_blockDegree_eq_one_four hL]
  norm_num

lemma sigmaPeriodicRandomWalkLaplacian_fromSupports_apply_eq_coord_overlap_card
    {L : ℕ} (hL : 2 ≤ L) (i j : SigmaCoord4 L) :
    randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L))) i j =
      (if i = j then 1 else 0) -
        4 *
          (((((coordPeriodicClosedTwoBlockOverlapCard i.1.1.1 j.1.1.1 *
            coordPeriodicClosedTwoBlockOverlapCard i.1.1.2 j.1.1.2) *
              coordPeriodicClosedTwoBlockOverlapCard i.1.2 j.1.2) *
                coordPeriodicClosedTwoBlockOverlapCard i.2 j.2) * 4 : ℕ) : ℝ) *
            (64 : ℝ)⁻¹ * (64 : ℝ)⁻¹ := by
  rw [sigmaPeriodicRandomWalkLaplacian_fromSupports_apply hL]
  rw [sigmaPeriodicCoarseOverlapMatrix_eq_coord_overlap_card hL]
  ring

lemma sigmaPeriodicBlockStarSupport4_adjacent_inter_nonempty {L : ℕ}
    {c d : SigmaCoord4 L} (h : (sigmaPeriodicCoarseGraph4 L).Adj c d) :
    (sigmaPeriodicBlockStarSupport4 L c ∩ sigmaPeriodicBlockStarSupport4 L d).Nonempty := by
  rcases sigmaPeriodicCoarseGraph4_adj_star_common h with ⟨a, hac, had⟩
  refine ⟨(a, 0), ?_⟩
  simp [sigmaPeriodicBlockStarSupport4, hac, had]

noncomputable def sigma4PeriodicBlockStarCovering (L : ℕ) (hL : 4 ≤ L) :
    SigmaBlockStarCovering (SigmaCoord4 L) (SigmaPeriodicFineEdge4 L) where
  coarseGraph := sigmaPeriodicCoarseGraph4 L
  fineEdgeSupport := sigmaPeriodicBlockStarSupport4 L
  support_nonempty := sigmaPeriodicBlockStarSupport4_nonempty L
  coarse_connected := sigmaPeriodicCoarseGraph4_connected L hL
  adjacent_share_fine_edge := sigmaPeriodicBlockStarSupport4_adjacent_inter_nonempty

noncomputable def sigma4PeriodicBlockStarRandomWalkLaplacian (L : ℕ) :
    Matrix (SigmaCoord4 L) (SigmaCoord4 L) ℝ :=
  if hL : 4 ≤ L then
    randomWalkLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport))
  else 0

noncomputable def sigma4PeriodicBlockStarLaplacianFamily : BoundaryLaplacianFamily where
  Node := SigmaCoord4
  nodeFintype := by
    intro L
    infer_instance
  nodeDecidableEq := by
    intro L
    infer_instance
  laplacian := sigma4PeriodicBlockStarRandomWalkLaplacian

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_of_four_le (L : ℕ) (hL : 4 ≤ L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L =
      randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport)) := by
  unfold sigma4PeriodicBlockStarRandomWalkLaplacian
  simp [hL]

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_isHermitian
    (L : ℕ) (hL : 4 ≤ L) :
    (sigma4PeriodicBlockStarRandomWalkLaplacian L).IsHermitian := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  let S : Matrix (SigmaCoord4 L) (SigmaCoord4 L) ℝ :=
    coarseOverlapMatrix
      (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L))
  have hsymm : S.IsSymm := by
    simpa [S] using
      (coarseOverlapMatrix_isSymm
        (blockAveragingMatrixFromSupports (sigmaPeriodicBlockStarSupport4 L)))
  have hdeg : ∀ i : SigmaCoord4 L, blockDegree S i = (1 / 4 : ℝ) := by
    intro i
    simpa [S] using sigmaPeriodicCoarseOverlapMatrix_blockDegree_eq_one_four hL2 i
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_of_four_le L hL]
  simpa [S, sigma4PeriodicBlockStarCovering] using
    realMatrix_isHermitian_of_isSymm
      (randomWalkLaplacian_isSymm_of_constant_blockDegree S hsymm hdeg)

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card
    (L : ℕ) (hL : 4 ≤ L) (i j : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i j =
      (if i = j then 1 else 0) -
        4 *
          (((((coordPeriodicClosedTwoBlockOverlapCard i.1.1.1 j.1.1.1 *
            coordPeriodicClosedTwoBlockOverlapCard i.1.1.2 j.1.1.2) *
              coordPeriodicClosedTwoBlockOverlapCard i.1.2 j.1.2) *
                coordPeriodicClosedTwoBlockOverlapCard i.2 j.2) * 4 : ℕ) : ℝ) *
            (64 : ℝ)⁻¹ * (64 : ℝ)⁻¹ := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_of_four_le L hL]
  simpa [sigma4PeriodicBlockStarCovering] using
    sigmaPeriodicRandomWalkLaplacian_fromSupports_apply_eq_coord_overlap_card
      hL2 i j

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_tensor_convolutionKernel
    (L : ℕ) (hL : 4 ≤ L) (i j : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i j =
      (if i = j then 1 else 0) -
        ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) := by
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL3
    i.1.1.1 j.1.1.1]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL3
    i.1.1.2 j.1.1.2]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL3
    i.1.2 j.1.2]
  rw [coordPeriodicClosedTwoBlockOverlapCard_eq_convolutionKernel hL3
    i.2 j.2]
  unfold sigmaPeriodicTensorConvolutionKernel4
  norm_num
  ring

lemma sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionKernel
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℝ)
    (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v i =
      v i -
        ∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j := by
  classical
  calc
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v i =
        ∑ j, sigma4PeriodicBlockStarRandomWalkLaplacian L i j * v j := by
      rfl
    _ = ∑ j,
          (((if i = j then 1 else 0) -
            ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256)) * v j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_tensor_convolutionKernel L hL]
    _ = ∑ j,
          ((if i = j then 1 else 0) * v j -
            ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    _ = (∑ j, (if i = j then 1 else 0) * v j) -
          ∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j := by
      rw [Finset.sum_sub_distrib]
    _ = v i -
          ∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j := by
      simp

lemma sigma4PeriodicBlockStarComplexMulVec_eq_tensor_convolutionKernel
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℂ)
    (i : SigmaCoord4 L) :
    realMatrixComplexMulVecLinearMap
        (sigma4PeriodicBlockStarRandomWalkLaplacian L) v i =
      v i -
        ∑ j, (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) * v j := by
  classical
  calc
    realMatrixComplexMulVecLinearMap
        (sigma4PeriodicBlockStarRandomWalkLaplacian L) v i =
        ∑ j, (sigma4PeriodicBlockStarRandomWalkLaplacian L i j : ℂ) * v j := by
      rw [realMatrixComplexMulVecLinearMap_apply]
    _ = ∑ j,
          ((((if i = j then 1 else 0 : ℝ) -
            ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256)) : ℂ) * v j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_tensor_convolutionKernel L hL]
      norm_num
    _ = ∑ j,
          (((if i = j then 1 else 0 : ℂ) * v j) -
            (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) * v j) := by
      refine Finset.sum_congr rfl ?_
      intro j _
      by_cases hij : i = j <;> simp [hij]
      ring
    _ = (∑ j, (if i = j then 1 else 0 : ℂ) * v j) -
          ∑ j, (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) * v j := by
      rw [Finset.sum_sub_distrib]
    _ = v i -
        ∑ j, (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) * v j := by
      simp

lemma sigmaPeriodicTensorConvolutionKernel4_sum_eq_support
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    (∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j) =
      (sigmaPeriodicTensorConvolutionSupport4 L i).sum
        (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j) := by
  classical
  let f : SigmaCoord4 L → ℝ := fun j =>
    ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j
  have hsubset :
      sigmaPeriodicTensorConvolutionSupport4 L i ⊆
        (Finset.univ : Finset (SigmaCoord4 L)) :=
    fun j _ => Finset.mem_univ j
  have hsum := Finset.sum_subset hsubset (f := f) ?_
  · simpa [f] using hsum.symm
  · intro j _ hjnot
    have hzero :=
      sigmaPeriodicTensorConvolutionKernel4_eq_zero_of_not_mem_support
        L i j hjnot
    simp [f, hzero]

lemma sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionSupport
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℝ)
    (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v i =
      v i - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
        (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j) := by
  rw [sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionKernel
    L hL]
  rw [sigmaPeriodicTensorConvolutionKernel4_sum_eq_support L v i]

noncomputable def sigma4PeriodicXAxisProfile {L : ℕ}
    (φ : Fin L → ℝ) : SigmaCoord4 L → ℝ :=
  fun i => φ i.1.1.1

lemma sigma4PeriodicXAxisProfile_tensorConvolutionKernel_sum {L : ℕ}
    (hL : 3 ≤ L) (φ : Fin L → ℝ) (i : SigmaCoord4 L) :
    (∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
        sigma4PeriodicXAxisProfile φ j) =
      (1 / 4 : ℝ) *
        (2 * φ i.1.1.1 + φ (coordPeriodicNext i.1.1.1) +
          φ (coordPeriodicPrev i.1.1.1)) := by
  classical
  let kx : Fin L → ℝ := fun x =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.1 x : ℝ)
  let ky : Fin L → ℝ := fun y =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.2 y : ℝ)
  let kz : Fin L → ℝ := fun z =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.2 z : ℝ)
  let kt : Fin L → ℝ := fun t =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.2 t : ℝ)
  have hprod := fourfold_univ_sum_product
    (fun x => kx x * φ x) ky kz kt
  have hx : (∑ x, kx x * φ x) =
      2 * φ i.1.1.1 + φ (coordPeriodicNext i.1.1.1) +
        φ (coordPeriodicPrev i.1.1.1) := by
    simpa [kx] using
      coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply hL i.1.1.1 φ
  have hy : (∑ y, ky y) = 4 := by
    simpa [ky] using
      coordPeriodicClosedTwoBlockConvolutionKernel_sum hL i.1.1.2
  have hz : (∑ z, kz z) = 4 := by
    simpa [kz] using
      coordPeriodicClosedTwoBlockConvolutionKernel_sum hL i.1.2
  have ht : (∑ t, kt t) = 4 := by
    simpa [kt] using
      coordPeriodicClosedTwoBlockConvolutionKernel_sum hL i.2
  calc
    (∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
        sigma4PeriodicXAxisProfile φ j) =
      (∑ j : SigmaCoord4 L,
        (((kx j.1.1.1 * φ j.1.1.1) * ky j.1.1.2) * kz j.1.2) *
          kt j.2 / 256) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [sigmaPeriodicTensorConvolutionKernel4, sigma4PeriodicXAxisProfile,
          kx, ky, kz, kt]
        ring_nf
    _ = ((((∑ x, kx x * φ x) * (∑ y, ky y)) * (∑ z, kz z)) *
        (∑ t, kt t)) / 256 := by
        rw [← Finset.sum_div]
        rw [← hprod]
    _ = (1 / 4 : ℝ) *
        (2 * φ i.1.1.1 + φ (coordPeriodicNext i.1.1.1) +
          φ (coordPeriodicPrev i.1.1.1)) := by
        rw [hx, hy, hz, ht]
        ring

lemma sigma4PeriodicXAxisProfile_laplacianMulVec_eq
    (L : ℕ) (hL : 4 ≤ L) (φ : Fin L → ℝ) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicXAxisProfile φ) i =
      φ i.1.1.1 -
        (1 / 4 : ℝ) *
          (2 * φ i.1.1.1 + φ (coordPeriodicNext i.1.1.1) +
            φ (coordPeriodicPrev i.1.1.1)) := by
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  rw [sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionKernel
    L hL]
  rw [sigma4PeriodicXAxisProfile_tensorConvolutionKernel_sum hL3 φ i]
  simp [sigma4PeriodicXAxisProfile]

noncomputable def coordPeriodicClosedTwoBlockConvolutionAction {L : ℕ}
    (a : Fin L) (φ : Fin L → ℝ) : ℝ :=
  ∑ b, (coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) * φ b

noncomputable def coordPeriodicClosedTwoBlockConvolutionActionComplex {L : ℕ}
    (a : Fin L) (φ : Fin L → ℂ) : ℂ :=
  ∑ b, ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) * φ b

lemma coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply_complex {L : ℕ}
    (hL : 3 ≤ L) (a : Fin L) (φ : Fin L → ℂ) :
    (∑ b, ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) * φ b) =
      2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
  classical
  let S : Finset (Fin L) := {a, coordPeriodicNext a, coordPeriodicPrev a}
  have hsubset : S ⊆ (Finset.univ : Finset (Fin L)) :=
    fun b _ => Finset.mem_univ b
  have hzero : ∀ b ∈ (Finset.univ : Finset (Fin L)), b ∉ S →
      ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) * φ b = 0 := by
    intro b _ hb
    have hba : b ≠ a := by
      intro h
      exact hb (by simp [S, h])
    have hbn : b ≠ coordPeriodicNext a := by
      intro h
      exact hb (by simp [S, h])
    have hbp : b ≠ coordPeriodicPrev a := by
      intro h
      exact hb (by simp [S, h])
    simp [coordPeriodicClosedTwoBlockConvolutionKernel, hba, hbn, hbp]
  calc
    (∑ b, ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) * φ b) =
        S.sum
          (fun b => ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) *
            φ b) := by
      exact (Finset.sum_subset hsubset hzero).symm
    _ = 2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
      have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 3) hL
      have hna : coordPeriodicNext a ≠ a := coordPeriodicNext_ne_self hL2 a
      have hpa : coordPeriodicPrev a ≠ a := by
        intro h
        have hn := coordPeriodicNext_prev a
        rw [h] at hn
        exact hna hn
      have hnp : coordPeriodicNext a ≠ coordPeriodicPrev a :=
        coordPeriodicNext_ne_prev_of_three_le hL a
      change ({a, coordPeriodicNext a, coordPeriodicPrev a} :
          Finset (Fin L)).sum
            (fun b => ((coordPeriodicClosedTwoBlockConvolutionKernel a b : ℝ) : ℂ) *
              φ b) =
        2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a)
      rw [Finset.sum_insert]
      · rw [Finset.sum_insert]
        · rw [Finset.sum_singleton]
          simp [coordPeriodicClosedTwoBlockConvolutionKernel, hna, hpa]
          ring
        · simp [hnp]
      · intro ha
        simp only [Finset.mem_singleton, Finset.mem_insert] at ha
        rcases ha with ha | ha
        · exact hna ha.symm
        · exact hpa ha.symm

lemma coordPeriodicClosedTwoBlockConvolutionAction_eq {L : ℕ}
    (hL : 3 ≤ L) (a : Fin L) (φ : Fin L → ℝ) :
    coordPeriodicClosedTwoBlockConvolutionAction a φ =
      2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
  exact coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply hL a φ

lemma coordPeriodicClosedTwoBlockConvolutionActionComplex_eq {L : ℕ}
    (hL : 3 ≤ L) (a : Fin L) (φ : Fin L → ℂ) :
    coordPeriodicClosedTwoBlockConvolutionActionComplex a φ =
      2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) := by
  exact coordPeriodicClosedTwoBlockConvolutionKernel_sum_apply_complex hL a φ

noncomputable def sigma4PeriodicTensorProductProfile {L : ℕ}
    (φx φy φz φt : Fin L → ℝ) : SigmaCoord4 L → ℝ :=
  fun i => (((φx i.1.1.1 * φy i.1.1.2) * φz i.1.2) * φt i.2)

noncomputable def sigma4PeriodicTensorProductProfileComplex {L : ℕ}
    (φx φy φz φt : Fin L → ℂ) : SigmaCoord4 L → ℂ :=
  fun i => (((φx i.1.1.1 * φy i.1.1.2) * φz i.1.2) * φt i.2)

lemma sigma4PeriodicTensorProductProfile_tensorConvolutionKernel_sum {L : ℕ}
    (φx φy φz φt : Fin L → ℝ) (i : SigmaCoord4 L) :
    (∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
        sigma4PeriodicTensorProductProfile φx φy φz φt j) =
      ((((coordPeriodicClosedTwoBlockConvolutionAction i.1.1.1 φx *
          coordPeriodicClosedTwoBlockConvolutionAction i.1.1.2 φy) *
            coordPeriodicClosedTwoBlockConvolutionAction i.1.2 φz) *
              coordPeriodicClosedTwoBlockConvolutionAction i.2 φt) / 256) := by
  classical
  let kx : Fin L → ℝ := fun x =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.1 x : ℝ)
  let ky : Fin L → ℝ := fun y =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.2 y : ℝ)
  let kz : Fin L → ℝ := fun z =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.1.2 z : ℝ)
  let kt : Fin L → ℝ := fun t =>
    (coordPeriodicClosedTwoBlockConvolutionKernel i.2 t : ℝ)
  have hprod := fourfold_univ_sum_product
    (fun x => kx x * φx x) (fun y => ky y * φy y)
    (fun z => kz z * φz z) (fun t => kt t * φt t)
  calc
    (∑ j, ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
        sigma4PeriodicTensorProductProfile φx φy φz φt j) =
      (∑ j : SigmaCoord4 L,
        ((((kx j.1.1.1 * φx j.1.1.1) *
            (ky j.1.1.2 * φy j.1.1.2)) *
              (kz j.1.2 * φz j.1.2)) *
                (kt j.2 * φt j.2)) / 256) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [sigmaPeriodicTensorConvolutionKernel4,
          sigma4PeriodicTensorProductProfile, kx, ky, kz, kt]
        ring_nf
    _ = ((((∑ x, kx x * φx x) * (∑ y, ky y * φy y)) *
          (∑ z, kz z * φz z)) * (∑ t, kt t * φt t)) / 256 := by
        rw [← Finset.sum_div]
        rw [← hprod]
    _ = ((((coordPeriodicClosedTwoBlockConvolutionAction i.1.1.1 φx *
          coordPeriodicClosedTwoBlockConvolutionAction i.1.1.2 φy) *
            coordPeriodicClosedTwoBlockConvolutionAction i.1.2 φz) *
              coordPeriodicClosedTwoBlockConvolutionAction i.2 φt) / 256) := by
        simp [coordPeriodicClosedTwoBlockConvolutionAction, kx, ky, kz, kt]

lemma sigma4PeriodicTensorProductProfileComplex_tensorConvolutionKernel_sum
    {L : ℕ}
    (φx φy φz φt : Fin L → ℂ) (i : SigmaCoord4 L) :
    (∑ j, (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) *
        sigma4PeriodicTensorProductProfileComplex φx φy φz φt j) =
      ((((coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.1.1 φx *
          coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.1.2 φy) *
            coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.2 φz) *
              coordPeriodicClosedTwoBlockConvolutionActionComplex i.2 φt) / 256) := by
  classical
  let kx : Fin L → ℂ := fun x =>
    ((coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.1 x : ℝ) : ℂ)
  let ky : Fin L → ℂ := fun y =>
    ((coordPeriodicClosedTwoBlockConvolutionKernel i.1.1.2 y : ℝ) : ℂ)
  let kz : Fin L → ℂ := fun z =>
    ((coordPeriodicClosedTwoBlockConvolutionKernel i.1.2 z : ℝ) : ℂ)
  let kt : Fin L → ℂ := fun t =>
    ((coordPeriodicClosedTwoBlockConvolutionKernel i.2 t : ℝ) : ℂ)
  have hprod := fourfold_univ_sum_product_complex
    (fun x => kx x * φx x) (fun y => ky y * φy y)
    (fun z => kz z * φz z) (fun t => kt t * φt t)
  calc
    (∑ j, (((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) : ℂ) / 256) *
        sigma4PeriodicTensorProductProfileComplex φx φy φz φt j) =
      (∑ j : SigmaCoord4 L,
        ((((kx j.1.1.1 * φx j.1.1.1) *
            (ky j.1.1.2 * φy j.1.1.2)) *
              (kz j.1.2 * φz j.1.2)) *
                (kt j.2 * φt j.2)) / 256) := by
        refine Finset.sum_congr rfl ?_
        intro j _
        simp [sigmaPeriodicTensorConvolutionKernel4,
          sigma4PeriodicTensorProductProfileComplex, kx, ky, kz, kt]
        ring_nf
    _ = ((((∑ x, kx x * φx x) * (∑ y, ky y * φy y)) *
          (∑ z, kz z * φz z)) * (∑ t, kt t * φt t)) / 256 := by
        rw [← Finset.sum_div]
        rw [← hprod]
    _ = ((((coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.1.1 φx *
          coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.1.2 φy) *
            coordPeriodicClosedTwoBlockConvolutionActionComplex i.1.2 φz) *
              coordPeriodicClosedTwoBlockConvolutionActionComplex i.2 φt) / 256) := by
        simp [coordPeriodicClosedTwoBlockConvolutionActionComplex, kx, ky, kz, kt]

def CoordPeriodicSecondNeighborEigenprofile {L : ℕ}
    (φ : Fin L → ℝ) (c : ℝ) : Prop :=
  ∀ a, φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) = 2 * c * φ a

lemma coordPeriodicClosedTwoBlockConvolutionAction_eq_of_secondNeighborEigenprofile
    {L : ℕ} (hL : 3 ≤ L) (φ : Fin L → ℝ) {c : ℝ}
    (hφ : CoordPeriodicSecondNeighborEigenprofile φ c) (a : Fin L) :
    coordPeriodicClosedTwoBlockConvolutionAction a φ = 2 * (1 + c) * φ a := by
  rw [coordPeriodicClosedTwoBlockConvolutionAction_eq hL a φ]
  have h := hφ a
  calc
    2 * φ a + φ (coordPeriodicNext a) + φ (coordPeriodicPrev a) =
        2 * φ a + (φ (coordPeriodicNext a) + φ (coordPeriodicPrev a)) := by
      ring
    _ = 2 * φ a + 2 * c * φ a := by rw [h]
    _ = 2 * (1 + c) * φ a := by ring

lemma sigma4PeriodicTensorProductProfile_laplacianMulVec_eq_of_secondNeighborEigenprofiles
    (L : ℕ) (hL : 4 ≤ L) (φx φy φz φt : Fin L → ℝ)
    {cx cy cz ct : ℝ}
    (hx : CoordPeriodicSecondNeighborEigenprofile φx cx)
    (hy : CoordPeriodicSecondNeighborEigenprofile φy cy)
    (hz : CoordPeriodicSecondNeighborEigenprofile φz cz)
    (ht : CoordPeriodicSecondNeighborEigenprofile φt ct) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicTensorProductProfile φx φy φz φt) =
      fun i =>
        (1 - ((((1 + cx) / 2 * ((1 + cy) / 2)) * ((1 + cz) / 2)) *
          ((1 + ct) / 2))) *
            sigma4PeriodicTensorProductProfile φx φy φz φt i := by
  ext i
  rw [sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionKernel
    L hL]
  rw [sigma4PeriodicTensorProductProfile_tensorConvolutionKernel_sum
    φx φy φz φt i]
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  rw [coordPeriodicClosedTwoBlockConvolutionAction_eq_of_secondNeighborEigenprofile
    hL3 φx hx]
  rw [coordPeriodicClosedTwoBlockConvolutionAction_eq_of_secondNeighborEigenprofile
    hL3 φy hy]
  rw [coordPeriodicClosedTwoBlockConvolutionAction_eq_of_secondNeighborEigenprofile
    hL3 φz hz]
  rw [coordPeriodicClosedTwoBlockConvolutionAction_eq_of_secondNeighborEigenprofile
    hL3 φt ht]
  simp [sigma4PeriodicTensorProductProfile]
  ring

noncomputable def periodicCosineAngle (L : ℕ) : ℝ :=
  (2 : ℝ) * Real.pi / (L : ℝ)

noncomputable def coordPeriodicCosineMode (L : ℕ) : Fin L → ℝ :=
  fun a => Real.cos (periodicCosineAngle L * (a.val : ℝ))

noncomputable def coordPeriodicCosineModeFreq (L : ℕ) (k : Fin L) :
    Fin L → ℝ :=
  fun a => Real.cos ((periodicCosineAngle L * (k.val : ℝ)) * (a.val : ℝ))

noncomputable def coordPeriodicSineModeFreq (L : ℕ) (k : Fin L) :
    Fin L → ℝ :=
  fun a => Real.sin ((periodicCosineAngle L * (k.val : ℝ)) * (a.val : ℝ))

lemma cos_add_add_cos_sub (x θ : ℝ) :
    Real.cos (x + θ) + Real.cos (x - θ) = 2 * Real.cos θ * Real.cos x := by
  rw [Real.cos_add, Real.cos_sub]
  ring

lemma sin_add_add_sin_sub (x θ : ℝ) :
    Real.sin (x + θ) + Real.sin (x - θ) = 2 * Real.cos θ * Real.sin x := by
  rw [Real.sin_add, Real.sin_sub]
  ring

lemma real_one_sub_cos_le_sq_div_two (x : ℝ) :
    1 - Real.cos x ≤ x ^ 2 / 2 := by
  have h := Real.one_sub_sq_div_two_le_cos (x := x)
  linarith

lemma periodicCosineAngle_mul_nat {L : ℕ} (hL : 0 < L) :
    periodicCosineAngle L * (L : ℝ) = 2 * Real.pi := by
  have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hL)
  unfold periodicCosineAngle
  field_simp [hLne]

lemma periodicCosineAngle_pos {L : ℕ} (hL : 4 ≤ L) :
    0 < periodicCosineAngle L := by
  unfold periodicCosineAngle
  positivity

lemma periodicCosineAngle_lt_two_pi {L : ℕ} (hL : 4 ≤ L) :
    periodicCosineAngle L < 2 * Real.pi := by
  have hLreal : (1 : ℝ) < (L : ℝ) := by
    exact_mod_cast (by omega : 1 < L)
  have hpos : 0 < 2 * Real.pi := by positivity
  unfold periodicCosineAngle
  nlinarith [div_lt_self hpos hLreal]

lemma periodicCosineEigenvalue_ne_zero {L : ℕ} (hL : 4 ≤ L) :
    ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ≠ 0 := by
  intro hμ
  let θ : ℝ := periodicCosineAngle L
  have hcos : Real.cos θ = 1 := by
    have hcos0 : Real.cos (periodicCosineAngle L) = 1 := by
      have hnum : 1 - Real.cos (periodicCosineAngle L) = 0 := by
        have hmul := congrArg (fun x : ℝ => x * 2) hμ
        ring_nf at hmul
        exact hmul
      linarith
    simpa [θ] using hcos0
  have hθpos : 0 < θ := by
    dsimp [θ]
    exact periodicCosineAngle_pos hL
  have hθlt : θ < 2 * Real.pi := by
    dsimp [θ]
    exact periodicCosineAngle_lt_two_pi hL
  have hθzero :=
    (Real.cos_eq_one_iff_of_lt_of_lt (by nlinarith [hθpos]) hθlt).1 hcos
  nlinarith

lemma periodicCosineEigenvalue_rescaled_le_pi_sq
    {L : ℕ} (hL : 4 ≤ L) :
    (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ≤
      Real.pi ^ 2 := by
  let θ : ℝ := periodicCosineAngle L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  have hθL : θ * (L : ℝ) = 2 * Real.pi := by
    simpa [θ] using periodicCosineAngle_mul_nat hLpos
  have hLreal_pos : 0 < (L : ℝ) := by positivity
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 :=
    real_one_sub_cos_le_sq_div_two θ
  have hμ : ((1 - Real.cos θ) / 2 : ℝ) ≤ θ ^ 2 / 4 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hμ (sq_nonneg (L : ℝ))
  have hcalc : (L : ℝ) ^ 2 * (θ ^ 2 / 4) = Real.pi ^ 2 := by
    have hLne : (L : ℝ) ≠ 0 := ne_of_gt hLreal_pos
    have hθ : θ = (2 * Real.pi) / (L : ℝ) := by
      exact (eq_div_iff hLne).2 hθL
    rw [hθ]
    field_simp [hLne]
    ring
  calc
    (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) =
        (L : ℝ) ^ 2 * ((1 - Real.cos θ) / 2 : ℝ) := by rfl
    _ ≤ (L : ℝ) ^ 2 * (θ ^ 2 / 4) := hmul
    _ = Real.pi ^ 2 := hcalc

theorem periodicCosineEigenvalue_rescaled_tendsto_pi_sq :
    Filter.Tendsto
      (fun L : ℕ =>
        (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ))
      Filter.atTop (nhds (Real.pi ^ 2)) := by
  have hx :
      Filter.Tendsto (fun L : ℕ => Real.pi / (L : ℝ))
        Filter.atTop (nhds 0) := by
    simpa using (tendsto_const_div_atTop_nhds_zero_nat (𝕜 := ℝ) Real.pi)
  have hdenom : ∀ᶠ L : ℕ in Filter.atTop, Real.pi / (L : ℝ) ≠ 0 := by
    exact Filter.eventually_atTop.mpr ⟨1, by
      intro L hL
      have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
      exact div_ne_zero Real.pi_ne_zero hLne⟩
  have hratio :
      Filter.Tendsto
        (fun L : ℕ => Real.sin (Real.pi / (L : ℝ)) / (Real.pi / (L : ℝ)))
        Filter.atTop (nhds 1) := by
    have heqv := Real.isEquivalent_sin.comp_tendsto hx
    exact (Asymptotics.isEquivalent_iff_tendsto_one hdenom).1 heqv
  have hmul :
      Filter.Tendsto (fun L : ℕ => (L : ℝ) * Real.sin (Real.pi / (L : ℝ)))
        Filter.atTop (nhds Real.pi) := by
    have hscaled :
        Filter.Tendsto
          (fun L : ℕ => Real.pi *
            (Real.sin (Real.pi / (L : ℝ)) / (Real.pi / (L : ℝ))))
          Filter.atTop (nhds (Real.pi * 1)) := by
      exact tendsto_const_nhds.mul hratio
    have hevent :
        (fun L : ℕ => (L : ℝ) * Real.sin (Real.pi / (L : ℝ))) =ᶠ[Filter.atTop]
          (fun L : ℕ => Real.pi *
            (Real.sin (Real.pi / (L : ℝ)) / (Real.pi / (L : ℝ)))) := by
      exact Filter.eventually_atTop.mpr ⟨1, by
        intro L hL
        have hLne : (L : ℝ) ≠ 0 := by exact_mod_cast (by omega : L ≠ 0)
        have hpLne : Real.pi / (L : ℝ) ≠ 0 := div_ne_zero Real.pi_ne_zero hLne
        field_simp [hLne, hpLne]⟩
    have hscaled' :
        Filter.Tendsto
          (fun L : ℕ => Real.pi *
            (Real.sin (Real.pi / (L : ℝ)) / (Real.pi / (L : ℝ))))
          Filter.atTop (nhds Real.pi) := by
      simpa using hscaled
    exact hscaled'.congr' hevent.symm
  have hsq :
      Filter.Tendsto
        (fun L : ℕ => ((L : ℝ) * Real.sin (Real.pi / (L : ℝ))) ^ 2)
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    simpa using hmul.pow 2
  refine hsq.congr' ?_
  exact Filter.eventually_atTop.mpr ⟨1, by
    intro L hL
    have hangle : periodicCosineAngle L = 2 * (Real.pi / (L : ℝ)) := by
      unfold periodicCosineAngle
      ring
    have hsin : ((1 - Real.cos (2 * (Real.pi / (L : ℝ)))) / 2 : ℝ) =
        Real.sin (Real.pi / (L : ℝ)) ^ 2 := by
      rw [Real.sin_sq_eq_half_sub]
      ring
    calc
      ((L : ℝ) * Real.sin (Real.pi / (L : ℝ))) ^ 2
          = (L : ℝ) ^ 2 * Real.sin (Real.pi / (L : ℝ)) ^ 2 := by ring
      _ = (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) := by
            rw [hangle, hsin]⟩

lemma coordPeriodicCosineMode_secondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) :
    CoordPeriodicSecondNeighborEigenprofile
      (coordPeriodicCosineMode L) (Real.cos (periodicCosineAngle L)) := by
  intro a
  let θ : ℝ := periodicCosineAngle L
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  have hθL : θ * (L : ℝ) = 2 * Real.pi := by
    simpa [θ] using periodicCosineAngle_mul_nat hLpos
  have hcos_step : ∀ n : ℕ,
      Real.cos (θ * ((n : ℝ) + 1)) + Real.cos (θ * ((n : ℝ) - 1)) =
        2 * Real.cos θ * Real.cos (θ * (n : ℝ)) := by
    intro n
    have h1 : θ * ((n : ℝ) + 1) = θ * (n : ℝ) + θ := by ring
    have h2 : θ * ((n : ℝ) - 1) = θ * (n : ℝ) - θ := by ring
    rw [h1, h2]
    exact cos_add_add_cos_sub (θ * (n : ℝ)) θ
  by_cases hzero : a.val = 0
  · have hn : (coordPeriodicNext a).val = a.val + 1 := by
      have hlt : a.val + 1 < L := by omega
      exact coordPeriodicNext_val_of_lt hlt
    have hp : (coordPeriodicPrev a).val = L - 1 := by
      have hpos : ¬ 0 < a.val := by omega
      exact coordPeriodicPrev_val_of_not_pos hpos
    have hprev_angle : θ * ((coordPeriodicPrev a).val : ℝ) = 2 * Real.pi - θ := by
      rw [hp]
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := Nat.cast_pred hLpos
      rw [hcast]
      linarith [hθL]
    have hnext_angle : θ * ((coordPeriodicNext a).val : ℝ) = θ := by
      rw [hn, hzero]
      norm_num
    simp only [coordPeriodicCosineMode]
    rw [hnext_angle, hprev_angle, Real.cos_two_pi_sub]
    simp [hzero, θ, periodicCosineAngle]
    ring
  · by_cases hlast : a.val + 1 = L
    · have hn : (coordPeriodicNext a).val = 0 := by
        have hnot : ¬ a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_not_lt hnot
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have haval : a.val = L - 1 := by omega
      have ha_angle : θ * (a.val : ℝ) = 2 * Real.pi - θ := by
        rw [haval]
        have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 := Nat.cast_pred hLpos
        rw [hcast]
        linarith [hθL]
      have hp_angle : θ * ((coordPeriodicPrev a).val : ℝ) =
          2 * Real.pi - 2 * θ := by
        rw [hp, haval]
        have hcast : ((L - 1 - 1 : ℕ) : ℝ) = (L : ℝ) - 2 := by
          have hnat : L - 1 - 1 = L - 2 := by omega
          rw [hnat]
          rw [Nat.cast_sub (by omega : 2 ≤ L)]
          norm_num
        rw [hcast]
        linarith [hθL]
      simp only [coordPeriodicCosineMode]
      rw [hn, hp_angle, ha_angle, Real.cos_two_pi_sub]
      norm_num
      change 1 + Real.cos (2 * θ) = 2 * Real.cos θ * Real.cos θ
      rw [Real.cos_two_mul]
      ring
    · have hn : (coordPeriodicNext a).val = a.val + 1 := by
        have hlt : a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_lt hlt
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have hprev_cast : ((a.val - 1 : ℕ) : ℝ) = (a.val : ℝ) - 1 := by
        exact Nat.cast_pred (by omega : 0 < a.val)
      have hnext_cast : ((a.val + 1 : ℕ) : ℝ) = (a.val : ℝ) + 1 := by
        norm_num
      simp only [coordPeriodicCosineMode]
      rw [hn, hp, hnext_cast, hprev_cast]
      simpa [θ] using hcos_step a.val

lemma coordPeriodicCosineModeFreq_secondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) (k : Fin L) :
    CoordPeriodicSecondNeighborEigenprofile
      (coordPeriodicCosineModeFreq L k)
      (Real.cos (periodicCosineAngle L * (k.val : ℝ))) := by
  intro a
  let θ : ℝ := periodicCosineAngle L * (k.val : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  have hbase : periodicCosineAngle L * (L : ℝ) = 2 * Real.pi :=
    periodicCosineAngle_mul_nat hLpos
  have hθL : θ * (L : ℝ) = (k.val : ℝ) * (2 * Real.pi) := by
    dsimp [θ]
    nlinarith
  have hcos_step : ∀ n : ℕ,
      Real.cos (θ * ((n : ℝ) + 1)) + Real.cos (θ * ((n : ℝ) - 1)) =
        2 * Real.cos θ * Real.cos (θ * (n : ℝ)) := by
    intro n
    have h1 : θ * ((n : ℝ) + 1) = θ * (n : ℝ) + θ := by ring
    have h2 : θ * ((n : ℝ) - 1) = θ * (n : ℝ) - θ := by ring
    rw [h1, h2]
    exact cos_add_add_cos_sub (θ * (n : ℝ)) θ
  by_cases hzero : a.val = 0
  · have hn : (coordPeriodicNext a).val = a.val + 1 := by
      have hlt : a.val + 1 < L := by omega
      exact coordPeriodicNext_val_of_lt hlt
    have hp : (coordPeriodicPrev a).val = L - 1 := by
      have hpos : ¬ 0 < a.val := by omega
      exact coordPeriodicPrev_val_of_not_pos hpos
    have hprev_angle : θ * ((coordPeriodicPrev a).val : ℝ) =
        (k.val : ℝ) * (2 * Real.pi) - θ := by
      rw [hp]
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 :=
        Nat.cast_pred hLpos
      rw [hcast]
      linarith [hθL]
    have hnext_angle : θ * ((coordPeriodicNext a).val : ℝ) = θ := by
      rw [hn, hzero]
      norm_num
    simp only [coordPeriodicCosineModeFreq]
    rw [hnext_angle, hprev_angle, Real.cos_nat_mul_two_pi_sub]
    simp [hzero, θ]
    ring
  · by_cases hlast : a.val + 1 = L
    · have hn : (coordPeriodicNext a).val = 0 := by
        have hnot : ¬ a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_not_lt hnot
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have haval : a.val = L - 1 := by omega
      have ha_angle : θ * (a.val : ℝ) =
          (k.val : ℝ) * (2 * Real.pi) - θ := by
        rw [haval]
        have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 :=
          Nat.cast_pred hLpos
        rw [hcast]
        linarith [hθL]
      have hp_angle : θ * ((coordPeriodicPrev a).val : ℝ) =
          (k.val : ℝ) * (2 * Real.pi) - 2 * θ := by
        rw [hp, haval]
        have hcast : ((L - 1 - 1 : ℕ) : ℝ) = (L : ℝ) - 2 := by
          have hnat : L - 1 - 1 = L - 2 := by omega
          rw [hnat]
          rw [Nat.cast_sub (by omega : 2 ≤ L)]
          norm_num
        rw [hcast]
        linarith [hθL]
      simp only [coordPeriodicCosineModeFreq]
      rw [hn, hp_angle, ha_angle]
      rw [Real.cos_nat_mul_two_pi_sub, Real.cos_nat_mul_two_pi_sub]
      norm_num
      change 1 + Real.cos (2 * θ) = 2 * Real.cos θ * Real.cos θ
      rw [Real.cos_two_mul]
      ring
    · have hn : (coordPeriodicNext a).val = a.val + 1 := by
        have hlt : a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_lt hlt
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have hprev_cast : ((a.val - 1 : ℕ) : ℝ) = (a.val : ℝ) - 1 := by
        exact Nat.cast_pred (by omega : 0 < a.val)
      have hnext_cast : ((a.val + 1 : ℕ) : ℝ) = (a.val : ℝ) + 1 := by
        norm_num
      simp only [coordPeriodicCosineModeFreq]
      rw [hn, hp, hnext_cast, hprev_cast]
      simpa [θ] using hcos_step a.val

lemma coordPeriodicSineModeFreq_secondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) (k : Fin L) :
    CoordPeriodicSecondNeighborEigenprofile
      (coordPeriodicSineModeFreq L k)
      (Real.cos (periodicCosineAngle L * (k.val : ℝ))) := by
  intro a
  let θ : ℝ := periodicCosineAngle L * (k.val : ℝ)
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  have hbase : periodicCosineAngle L * (L : ℝ) = 2 * Real.pi :=
    periodicCosineAngle_mul_nat hLpos
  have hθL : θ * (L : ℝ) = (k.val : ℝ) * (2 * Real.pi) := by
    dsimp [θ]
    nlinarith
  have hsin_step : ∀ n : ℕ,
      Real.sin (θ * ((n : ℝ) + 1)) + Real.sin (θ * ((n : ℝ) - 1)) =
        2 * Real.cos θ * Real.sin (θ * (n : ℝ)) := by
    intro n
    have h1 : θ * ((n : ℝ) + 1) = θ * (n : ℝ) + θ := by ring
    have h2 : θ * ((n : ℝ) - 1) = θ * (n : ℝ) - θ := by ring
    rw [h1, h2]
    exact sin_add_add_sin_sub (θ * (n : ℝ)) θ
  by_cases hzero : a.val = 0
  · have hn : (coordPeriodicNext a).val = a.val + 1 := by
      have hlt : a.val + 1 < L := by omega
      exact coordPeriodicNext_val_of_lt hlt
    have hp : (coordPeriodicPrev a).val = L - 1 := by
      have hpos : ¬ 0 < a.val := by omega
      exact coordPeriodicPrev_val_of_not_pos hpos
    have hprev_angle : θ * ((coordPeriodicPrev a).val : ℝ) =
        (k.val : ℝ) * (2 * Real.pi) - θ := by
      rw [hp]
      have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 :=
        Nat.cast_pred hLpos
      rw [hcast]
      linarith [hθL]
    have hnext_angle : θ * ((coordPeriodicNext a).val : ℝ) = θ := by
      rw [hn, hzero]
      norm_num
    simp only [coordPeriodicSineModeFreq]
    rw [hnext_angle, hprev_angle, Real.sin_nat_mul_two_pi_sub]
    simp [hzero]
  · by_cases hlast : a.val + 1 = L
    · have hn : (coordPeriodicNext a).val = 0 := by
        have hnot : ¬ a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_not_lt hnot
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have haval : a.val = L - 1 := by omega
      have ha_angle : θ * (a.val : ℝ) =
          (k.val : ℝ) * (2 * Real.pi) - θ := by
        rw [haval]
        have hcast : ((L - 1 : ℕ) : ℝ) = (L : ℝ) - 1 :=
          Nat.cast_pred hLpos
        rw [hcast]
        linarith [hθL]
      have hp_angle : θ * ((coordPeriodicPrev a).val : ℝ) =
          (k.val : ℝ) * (2 * Real.pi) - 2 * θ := by
        rw [hp, haval]
        have hcast : ((L - 1 - 1 : ℕ) : ℝ) = (L : ℝ) - 2 := by
          have hnat : L - 1 - 1 = L - 2 := by omega
          rw [hnat]
          rw [Nat.cast_sub (by omega : 2 ≤ L)]
          norm_num
        rw [hcast]
        linarith [hθL]
      simp only [coordPeriodicSineModeFreq]
      rw [hn, hp_angle, ha_angle]
      rw [Real.sin_nat_mul_two_pi_sub, Real.sin_nat_mul_two_pi_sub]
      norm_num
      rw [Real.sin_two_mul]
      ring
    · have hn : (coordPeriodicNext a).val = a.val + 1 := by
        have hlt : a.val + 1 < L := by omega
        exact coordPeriodicNext_val_of_lt hlt
      have hp : (coordPeriodicPrev a).val = a.val - 1 := by
        have hpos : 0 < a.val := by omega
        exact coordPeriodicPrev_val_of_pos hpos
      have hprev_cast : ((a.val - 1 : ℕ) : ℝ) = (a.val : ℝ) - 1 := by
        exact Nat.cast_pred (by omega : 0 < a.val)
      have hnext_cast : ((a.val + 1 : ℕ) : ℝ) = (a.val : ℝ) + 1 := by
        norm_num
      simp only [coordPeriodicSineModeFreq]
      rw [hn, hp, hnext_cast, hprev_cast]
      simpa [θ] using hsin_step a.val

noncomputable def coordPeriodicTrigModeFreq (useSine : Bool)
    (L : ℕ) (k : Fin L) : Fin L → ℝ :=
  if useSine then coordPeriodicSineModeFreq L k else coordPeriodicCosineModeFreq L k

lemma coordPeriodicTrigModeFreq_secondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) (useSine : Bool) (k : Fin L) :
    CoordPeriodicSecondNeighborEigenprofile
      (coordPeriodicTrigModeFreq useSine L k)
      (Real.cos (periodicCosineAngle L * (k.val : ℝ))) := by
  cases useSine <;>
    simp [coordPeriodicTrigModeFreq,
      coordPeriodicCosineModeFreq_secondNeighborEigenprofile hL k,
      coordPeriodicSineModeFreq_secondNeighborEigenprofile hL k]

lemma sigma4PeriodicXAxisProfile_laplacianMulVec_eq_of_secondNeighborEigenprofile
    (L : ℕ) (hL : 4 ≤ L) (φ : Fin L → ℝ) {c : ℝ}
    (hφ : CoordPeriodicSecondNeighborEigenprofile φ c) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicXAxisProfile φ) =
      fun i => ((1 - c) / 2) * sigma4PeriodicXAxisProfile φ i := by
  ext i
  rw [sigma4PeriodicXAxisProfile_laplacianMulVec_eq L hL φ i]
  have hx := hφ i.1.1.1
  calc
    φ i.1.1.1 -
        (1 / 4 : ℝ) *
          (2 * φ i.1.1.1 + φ (coordPeriodicNext i.1.1.1) +
            φ (coordPeriodicPrev i.1.1.1)) =
        φ i.1.1.1 -
          (1 / 4 : ℝ) *
            (2 * φ i.1.1.1 +
              (φ (coordPeriodicNext i.1.1.1) +
                φ (coordPeriodicPrev i.1.1.1))) := by
      ring
    _ = φ i.1.1.1 -
          (1 / 4 : ℝ) * (2 * φ i.1.1.1 + 2 * c * φ i.1.1.1) := by
      rw [hx]
    _ = ((1 - c) / 2) * sigma4PeriodicXAxisProfile φ i := by
      simp [sigma4PeriodicXAxisProfile]
      ring

lemma sigma4PeriodicXAxisProfile_secondNeighborEigenvalue_mem_spectralSet
    (L : ℕ) (hL : 4 ≤ L) (φ : Fin L → ℝ) {c : ℝ}
    (hvne : sigma4PeriodicXAxisProfile φ ≠ 0)
    (hφ : CoordPeriodicSecondNeighborEigenprofile φ c) :
    ((1 - c) / 2 : ℝ) ∈
      sigma4PeriodicBlockStarLaplacianFamily.spectralSet L := by
  exact sigma4PeriodicBlockStarLaplacianFamily.mem_spectralSet_of_eigenmode
    L hvne
    (sigma4PeriodicXAxisProfile_laplacianMulVec_eq_of_secondNeighborEigenprofile
      L hL φ hφ)

lemma sigma4PeriodicCosineXAxisProfile_ne_zero
    {L : ℕ} (hL : 4 ≤ L) :
    sigma4PeriodicXAxisProfile (coordPeriodicCosineMode L) ≠ 0 := by
  intro hzero
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  let z : Fin L := ⟨0, hLpos⟩
  let i : SigmaCoord4 L := (((z, z), z), z)
  have hval := congrFun hzero i
  simp [sigma4PeriodicXAxisProfile, coordPeriodicCosineMode, periodicCosineAngle,
    i, z] at hval

theorem sigma4PeriodicCosineXAxisProfile_laplacianMulVec_eq
    (L : ℕ) (hL : 4 ≤ L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicXAxisProfile (coordPeriodicCosineMode L)) =
      fun i =>
        ((1 - Real.cos (periodicCosineAngle L)) / 2) *
          sigma4PeriodicXAxisProfile (coordPeriodicCosineMode L) i := by
  exact sigma4PeriodicXAxisProfile_laplacianMulVec_eq_of_secondNeighborEigenprofile
    L hL (coordPeriodicCosineMode L)
    (coordPeriodicCosineMode_secondNeighborEigenprofile hL)

lemma sigma4PeriodicCosineXAxisProfile_eigenvalue_mem_spectralSet
    (L : ℕ) (hL : 4 ≤ L) :
    ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ∈
      sigma4PeriodicBlockStarLaplacianFamily.spectralSet L := by
  exact sigma4PeriodicXAxisProfile_secondNeighborEigenvalue_mem_spectralSet
    L hL (coordPeriodicCosineMode L)
    (sigma4PeriodicCosineXAxisProfile_ne_zero hL)
    (coordPeriodicCosineMode_secondNeighborEigenprofile hL)

noncomputable def sigma4PeriodicTensorConvolutionRowStencilCenter
    (L : ℕ) (_ : SigmaCoord4 L) : ℝ :=
  if 4 ≤ L then 1 else 0

noncomputable def sigma4PeriodicTensorConvolutionRowStencilWeight
    (L : ℕ) (i j : SigmaCoord4 L) : ℝ :=
  if 4 ≤ L then (sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256 else 0

noncomputable def sigma4PeriodicTensorConvolutionRowStencil (L : ℕ) :
    BoundaryRowStencilAt sigma4PeriodicBlockStarLaplacianFamily L (SigmaCoord4 L) where
  center := sigma4PeriodicTensorConvolutionRowStencilCenter L
  weight := sigma4PeriodicTensorConvolutionRowStencilWeight L
  shift := fun j _ => j
  laplacian_apply := by
    intro v i
    by_cases hL : 4 ≤ L
    · rw [
        sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionKernel
          L hL]
      simp [sigma4PeriodicTensorConvolutionRowStencilCenter,
        sigma4PeriodicTensorConvolutionRowStencilWeight, hL]
    · unfold BoundaryLaplacianFamily.laplacianMulVec
      simp [sigma4PeriodicBlockStarLaplacianFamily,
        sigma4PeriodicBlockStarRandomWalkLaplacian,
        sigma4PeriodicTensorConvolutionRowStencilCenter,
        sigma4PeriodicTensorConvolutionRowStencilWeight, hL]
      rfl

lemma sigma4PeriodicTensorConvolutionRowStencil_rowAction_eq_support
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℝ)
    (i : SigmaCoord4 L) :
    (sigma4PeriodicTensorConvolutionRowStencil L).rowAction v i =
      v i - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
        (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * v j) := by
  rw [(sigma4PeriodicTensorConvolutionRowStencil L).rowAction_eq_laplacianMulVec]
  rw [
    sigma4PeriodicBlockStarLaplacianFamily_laplacianMulVec_eq_tensor_convolutionSupport
      L hL]

lemma sigma4PeriodicTensorConvolutionRowStencil_rayleighNumerator_eq_support
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℝ) :
    (sigma4PeriodicTensorConvolutionRowStencil L).rayleighNumerator v =
      ∑ i,
        v i *
          (v i - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
            (fun j =>
              ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
                v j)) := by
  classical
  unfold BoundaryRowStencilAt.rayleighNumerator
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sigma4PeriodicTensorConvolutionRowStencil_rowAction_eq_support
    L hL v i]

lemma sigma4PeriodicBlockStarLaplacianFamily_nodeDot_laplacianMulVec_eq_support
    (L : ℕ) (hL : 4 ≤ L) (v : SigmaCoord4 L → ℝ) :
    sigma4PeriodicBlockStarLaplacianFamily.nodeDot L v
        (sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v) =
      ∑ i,
        v i *
          (v i - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
            (fun j =>
              ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
                v j)) := by
  rw [← (sigma4PeriodicTensorConvolutionRowStencil L)
    |>.rayleighNumerator_eq_nodeDot_laplacianMulVec v]
  exact sigma4PeriodicTensorConvolutionRowStencil_rayleighNumerator_eq_support
    L hL v

lemma sigma4PeriodicTensorConvolutionRowStencil_symbol_apply_of_four_le
    (L : ℕ) (hL : 4 ≤ L)
    (phase : SigmaCoord4 L → SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    (sigma4PeriodicTensorConvolutionRowStencil L).symbol phase i =
      1 - ∑ j,
        ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) * phase j i := by
  simp [BoundaryRowStencilAt.symbol, sigma4PeriodicTensorConvolutionRowStencil,
    sigma4PeriodicTensorConvolutionRowStencilCenter,
    sigma4PeriodicTensorConvolutionRowStencilWeight, hL]

lemma sigma4PeriodicTensorConvolutionRowStencil_symbol_eq_support
    (L : ℕ) (hL : 4 ≤ L)
    (phase : SigmaCoord4 L → SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    (sigma4PeriodicTensorConvolutionRowStencil L).symbol phase i =
      1 - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
        (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
          phase j i) := by
  rw [sigma4PeriodicTensorConvolutionRowStencil_symbol_apply_of_four_le
    L hL phase i]
  rw [sigmaPeriodicTensorConvolutionKernel4_sum_eq_support
    L (fun j => phase j i) i]

lemma sigma4PeriodicTensorConvolutionRowStencil_eigenmode_eq
    (L : ℕ) {v : SigmaCoord4 L → ℝ}
    {phase : SigmaCoord4 L → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hshift : ∀ j i, v j = phase j i * v i)
    (hsymbol :
      ∀ i, (sigma4PeriodicTensorConvolutionRowStencil L).symbol phase i = μ) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v =
      fun i => μ * v i := by
  exact (sigma4PeriodicTensorConvolutionRowStencil L).eigenmode_eq_of_symbol_eq
    hshift hsymbol

lemma sigma4PeriodicTensorConvolutionRowStencil_eigenmode_eq_of_support_symbol
    (L : ℕ) (hL : 4 ≤ L) {v : SigmaCoord4 L → ℝ}
    {phase : SigmaCoord4 L → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hshift : ∀ j i, v j = phase j i * v i)
    (hsymbol :
      ∀ i,
        1 - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
          (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
            phase j i) = μ) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v =
      fun i => μ * v i := by
  refine sigma4PeriodicTensorConvolutionRowStencil_eigenmode_eq
    L hshift ?_
  intro i
  rw [sigma4PeriodicTensorConvolutionRowStencil_symbol_eq_support
    L hL phase i]
  exact hsymbol i

lemma sigma4PeriodicTensorConvolutionRowStencil_mem_spectralSet_of_support_symbol
    (L : ℕ) (hL : 4 ≤ L) {v : SigmaCoord4 L → ℝ}
    {phase : SigmaCoord4 L → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ j i, v j = phase j i * v i)
    (hsymbol :
      ∀ i,
        1 - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
          (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
            phase j i) = μ) :
    μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L := by
  exact (sigma4PeriodicTensorConvolutionRowStencil L).mem_spectralSet_of_symbol_eigenmode
    hvne hshift (by
      intro i
      rw [sigma4PeriodicTensorConvolutionRowStencil_symbol_eq_support
        L hL phase i]
      exact hsymbol i)

def sigmaCoord4PeriodicNextX {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((coordPeriodicNext i.1.1.1, i.1.1.2), i.1.2), i.2)

def sigmaCoord4PeriodicPrevX {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((coordPeriodicPrev i.1.1.1, i.1.1.2), i.1.2), i.2)

def sigmaCoord4PeriodicNextY {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, coordPeriodicNext i.1.1.2), i.1.2), i.2)

def sigmaCoord4PeriodicPrevY {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, coordPeriodicPrev i.1.1.2), i.1.2), i.2)

def sigmaCoord4PeriodicNextZ {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, i.1.1.2), coordPeriodicNext i.1.2), i.2)

def sigmaCoord4PeriodicPrevZ {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, i.1.1.2), coordPeriodicPrev i.1.2), i.2)

def sigmaCoord4PeriodicNextT {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, i.1.1.2), i.1.2), coordPeriodicNext i.2)

def sigmaCoord4PeriodicPrevT {L : ℕ} (i : SigmaCoord4 L) : SigmaCoord4 L :=
  (((i.1.1.1, i.1.1.2), i.1.2), coordPeriodicPrev i.2)

lemma sigmaCoord4PeriodicNextX_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicNextX i ≠ i := by
  intro h
  have hx := congrArg (fun p : SigmaCoord4 L => p.1.1.1) h
  exact coordPeriodicNext_ne_self hL i.1.1.1 hx

lemma sigmaCoord4PeriodicPrevX_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicPrevX i ≠ i := by
  intro h
  have hx := congrArg (fun p : SigmaCoord4 L => p.1.1.1) h
  exact coordPeriodicPrev_ne_self hL i.1.1.1 hx

lemma sigmaCoord4PeriodicNextY_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicNextY i ≠ i := by
  intro h
  have hy := congrArg (fun p : SigmaCoord4 L => p.1.1.2) h
  exact coordPeriodicNext_ne_self hL i.1.1.2 hy

lemma sigmaCoord4PeriodicPrevY_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicPrevY i ≠ i := by
  intro h
  have hy := congrArg (fun p : SigmaCoord4 L => p.1.1.2) h
  exact coordPeriodicPrev_ne_self hL i.1.1.2 hy

lemma sigmaCoord4PeriodicNextZ_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicNextZ i ≠ i := by
  intro h
  have hz := congrArg (fun p : SigmaCoord4 L => p.1.2) h
  exact coordPeriodicNext_ne_self hL i.1.2 hz

lemma sigmaCoord4PeriodicPrevZ_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicPrevZ i ≠ i := by
  intro h
  have hz := congrArg (fun p : SigmaCoord4 L => p.1.2) h
  exact coordPeriodicPrev_ne_self hL i.1.2 hz

lemma sigmaCoord4PeriodicNextT_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicNextT i ≠ i := by
  intro h
  have ht := congrArg (fun p : SigmaCoord4 L => p.2) h
  exact coordPeriodicNext_ne_self hL i.2 ht

lemma sigmaCoord4PeriodicPrevT_ne {L : ℕ} (hL : 2 ≤ L)
    (i : SigmaCoord4 L) :
    sigmaCoord4PeriodicPrevT i ≠ i := by
  intro h
  have ht := congrArg (fun p : SigmaCoord4 L => p.2) h
  exact coordPeriodicPrev_ne_self hL i.2 ht

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_self
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i i = (15 / 16 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [coordPeriodicClosedTwoBlockOverlapCard_self hL2]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_nextX
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicNextX i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicNextX i :=
    (sigmaCoord4PeriodicNextX_ne hL2 i).symm
  have hne' :
      ¬ i = (((coordPeriodicNext i.1.1.1, i.1.1.2), i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicNextX] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicNextX, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_next hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_prevX
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicPrevX i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicPrevX i :=
    (sigmaCoord4PeriodicPrevX_ne hL2 i).symm
  have hne' :
      ¬ i = (((coordPeriodicPrev i.1.1.1, i.1.1.2), i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicPrevX] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicPrevX, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_prev hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_nextY
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicNextY i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicNextY i :=
    (sigmaCoord4PeriodicNextY_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, coordPeriodicNext i.1.1.2), i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicNextY] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicNextY, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_next hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_prevY
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicPrevY i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicPrevY i :=
    (sigmaCoord4PeriodicPrevY_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, coordPeriodicPrev i.1.1.2), i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicPrevY] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicPrevY, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_prev hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_nextZ
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicNextZ i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicNextZ i :=
    (sigmaCoord4PeriodicNextZ_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, i.1.1.2), coordPeriodicNext i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicNextZ] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicNextZ, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_next hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_prevZ
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicPrevZ i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicPrevZ i :=
    (sigmaCoord4PeriodicPrevZ_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, i.1.1.2), coordPeriodicPrev i.1.2), i.2) := by
    simpa [sigmaCoord4PeriodicPrevZ] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicPrevZ, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_prev hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_nextT
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicNextT i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicNextT i :=
    (sigmaCoord4PeriodicNextT_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, i.1.1.2), i.1.2), coordPeriodicNext i.2) := by
    simpa [sigmaCoord4PeriodicNextT] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicNextT, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_next hL3]
  norm_num

lemma sigma4PeriodicBlockStarRandomWalkLaplacian_apply_prevT
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicBlockStarRandomWalkLaplacian L i
      (sigmaCoord4PeriodicPrevT i) = (-1 / 32 : ℝ) := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  have hne : i ≠ sigmaCoord4PeriodicPrevT i :=
    (sigmaCoord4PeriodicPrevT_ne hL2 i).symm
  have hne' :
      ¬ i = (((i.1.1.1, i.1.1.2), i.1.2), coordPeriodicPrev i.2) := by
    simpa [sigmaCoord4PeriodicPrevT] using hne
  rw [sigma4PeriodicBlockStarRandomWalkLaplacian_apply_eq_coord_overlap_card L hL]
  simp [sigmaCoord4PeriodicPrevT, hne',
    coordPeriodicClosedTwoBlockOverlapCard_self hL2,
    coordPeriodicClosedTwoBlockOverlapCard_prev hL3]
  norm_num

theorem sigma4PeriodicBlockStarLaplacianFamily_spectrum_nonneg
    (L : ℕ) (hL : 4 ≤ L) :
    ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L, 0 ≤ μ := by
  have hnonneg :=
    (sigmaBlockStarCovering_blockLaplacian (sigma4PeriodicBlockStarCovering L hL)).2.1
  intro μ hμ
  exact hnonneg μ (by
    simpa [BoundaryLaplacianFamily.spectralSet, sigma4PeriodicBlockStarLaplacianFamily,
      sigma4PeriodicBlockStarRandomWalkLaplacian, hL] using hμ)

theorem sigma4PeriodicBlockStarLaplacianFamily_positive_spectral_gap
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L, μ ≠ 0 → γ ≤ μ := by
  have hgap :=
    sigmaBlockStarCovering_positive_spectral_gap (sigma4PeriodicBlockStarCovering L hL)
  simpa [BoundaryLaplacianFamily.spectralSet, sigma4PeriodicBlockStarLaplacianFamily,
    sigma4PeriodicBlockStarRandomWalkLaplacian, hL] using hgap

theorem sigma4PeriodicBlockStarLaplacianFamily_exists_nonzero_spectral_value
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ μ : ℝ, μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L ∧ μ ≠ 0 := by
  haveI : Nontrivial (SigmaCoord4 L) := sigmaCoord4_nontrivial_of_four_le L hL
  have hnonzero :=
    sigmaBlockStarCovering_exists_nonzero_spectral_value
      (sigma4PeriodicBlockStarCovering L hL)
  simpa [BoundaryLaplacianFamily.spectralSet, sigma4PeriodicBlockStarLaplacianFamily,
    sigma4PeriodicBlockStarRandomWalkLaplacian, hL] using hnonzero

noncomputable def sigma4PeriodicBlockStarSpectrallyClosedFamily :
    SpectrallyClosedBoundaryLaplacianFamily where
  family := sigma4PeriodicBlockStarLaplacianFamily
  spectrum_nonneg := by
    intro L hL
    exact sigma4PeriodicBlockStarLaplacianFamily_spectrum_nonneg L hL
  positive_spectral_gap := by
    intro L hL
    exact sigma4PeriodicBlockStarLaplacianFamily_positive_spectral_gap L hL

noncomputable def sigma4PeriodicBlockStarNonzeroSpectralValueExistsFrom :
    BoundaryNonzeroSpectralValueExistsFrom sigma4PeriodicBlockStarLaplacianFamily 4 where
  L0_ge_four := le_rfl
  exists_nonzero := by
    intro L hL
    exact sigma4PeriodicBlockStarLaplacianFamily_exists_nonzero_spectral_value L hL

noncomputable def sigma4OpenFirstPositiveSpectralValueFrom
    {L0 : ℕ}
    (E :
      BoundaryNonzeroSpectralValueExistsFrom
        sigma4BlockStarOpenLaplacianFamily L0) :
    ℕ → ℝ :=
  firstPositiveSpectralValueFrom sigma4BlockStarOpenSpectrallyClosedFamily E

noncomputable def sigma4OpenFirstPositiveSpectralValueRealizationFrom
    {L0 : ℕ}
    (E :
      BoundaryNonzeroSpectralValueExistsFrom
        sigma4BlockStarOpenLaplacianFamily L0) :
    BoundarySpectralValueRealizationFrom sigma4BlockStarOpenLaplacianFamily
      (sigma4OpenFirstPositiveSpectralValueFrom E) L0 :=
  firstPositiveSpectralValueRealizationFrom
    sigma4BlockStarOpenSpectrallyClosedFamily E

noncomputable def sigma4PeriodicFirstPositiveSpectralValueFrom
    {L0 : ℕ}
    (E :
      BoundaryNonzeroSpectralValueExistsFrom
        sigma4PeriodicBlockStarLaplacianFamily L0) :
    ℕ → ℝ :=
  firstPositiveSpectralValueFrom sigma4PeriodicBlockStarSpectrallyClosedFamily E

noncomputable def sigma4PeriodicFirstPositiveSpectralValueRealizationFrom
    {L0 : ℕ}
    (E :
      BoundaryNonzeroSpectralValueExistsFrom
        sigma4PeriodicBlockStarLaplacianFamily L0) :
    BoundarySpectralValueRealizationFrom sigma4PeriodicBlockStarLaplacianFamily
      (sigma4PeriodicFirstPositiveSpectralValueFrom E) L0 :=
  firstPositiveSpectralValueRealizationFrom
    sigma4PeriodicBlockStarSpectrallyClosedFamily E

noncomputable def sigma4OpenFirstPositiveSpectralValue : ℕ → ℝ :=
  sigma4OpenFirstPositiveSpectralValueFrom
    sigma4BlockStarOpenNonzeroSpectralValueExistsFrom

noncomputable def sigma4OpenFirstPositiveSpectralValueRealization :
    BoundarySpectralValueRealizationFrom sigma4BlockStarOpenLaplacianFamily
      sigma4OpenFirstPositiveSpectralValue 4 :=
  sigma4OpenFirstPositiveSpectralValueRealizationFrom
    sigma4BlockStarOpenNonzeroSpectralValueExistsFrom

noncomputable def sigma4PeriodicFirstPositiveSpectralValue : ℕ → ℝ :=
  sigma4PeriodicFirstPositiveSpectralValueFrom
    sigma4PeriodicBlockStarNonzeroSpectralValueExistsFrom

noncomputable def sigma4PeriodicFirstPositiveSpectralValueRealization :
    BoundarySpectralValueRealizationFrom sigma4PeriodicBlockStarLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue 4 :=
  sigma4PeriodicFirstPositiveSpectralValueRealizationFrom
    sigma4PeriodicBlockStarNonzeroSpectralValueExistsFrom

theorem sigma4OpenFirstPositiveSpectralValue_le_of_eigenmode
    {L : ℕ} (hL : 4 ≤ L) {μ : ℝ}
    {v : SigmaCoord4 L → ℝ}
    (hvne : v ≠ 0)
    (heig :
      sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L v =
        fun i => μ * v i)
    (hμne : μ ≠ 0) :
    sigma4OpenFirstPositiveSpectralValue L ≤ μ := by
  exact sigma4OpenFirstPositiveSpectralValueRealization.le_of_eigenmode
    hL hvne heig hμne

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_eigenmode
    {L : ℕ} (hL : 4 ≤ L) {μ : ℝ}
    {v : SigmaCoord4 L → ℝ}
    (hvne : v ≠ 0)
    (heig :
      sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v =
        fun i => μ * v i)
    (hμne : μ ≠ 0) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤ μ := by
  exact sigma4PeriodicFirstPositiveSpectralValueRealization.le_of_eigenmode
    hL hvne heig hμne

theorem sigma4OpenFirstPositiveSpectralValue_rescaled_upper_of_eigenmode
    {L : ℕ} (hL : 4 ≤ L) {μ coefficient upperError : ℝ}
    {v : SigmaCoord4 L → ℝ}
    (hvne : v ≠ 0)
    (heig :
      sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L v =
        fun i => μ * v i)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4OpenFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    sigma4OpenFirstPositiveSpectralValueRealization
      |>.rescaled_value_upper_of_eigenmode hL hvne heig hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_eigenmode
    {L : ℕ} (hL : 4 ≤ L) {μ coefficient upperError : ℝ}
    {v : SigmaCoord4 L → ℝ}
    (hvne : v ≠ 0)
    (heig :
      sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v =
        fun i => μ * v i)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    sigma4PeriodicFirstPositiveSpectralValueRealization
      |>.rescaled_value_upper_of_eigenmode hL hvne heig hμne hupper

theorem sigma4OpenFirstPositiveSpectralValue_le_of_scalarStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt sigma4BlockStarOpenLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ} {phase : Offset → ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0) :
    sigma4OpenFirstPositiveSpectralValue L ≤ S.eigenvalue phase := by
  exact BoundarySpectralValueRealizationFrom.le_of_scalarStencilEigenmode
    sigma4OpenFirstPositiveSpectralValueRealization hL S hvne hshift hμne

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_scalarStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt sigma4PeriodicBlockStarLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ} {phase : Offset → ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤ S.eigenvalue phase := by
  exact BoundarySpectralValueRealizationFrom.le_of_scalarStencilEigenmode
    sigma4PeriodicFirstPositiveSpectralValueRealization hL S hvne hshift hμne

theorem sigma4OpenFirstPositiveSpectralValue_rescaled_upper_of_scalarStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt sigma4BlockStarOpenLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ} {phase : Offset → ℝ}
    {coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0)
    (hupper :
      (L : ℝ) ^ 2 * S.eigenvalue phase ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4OpenFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    BoundarySpectralValueRealizationFrom.rescaled_value_upper_of_scalarStencilEigenmode
      sigma4OpenFirstPositiveSpectralValueRealization hL S hvne hshift hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_scalarStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryScalarStencilAt sigma4PeriodicBlockStarLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ} {phase : Offset → ℝ}
    {coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ * v i)
    (hμne : S.eigenvalue phase ≠ 0)
    (hupper :
      (L : ℝ) ^ 2 * S.eigenvalue phase ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    BoundarySpectralValueRealizationFrom.rescaled_value_upper_of_scalarStencilEigenmode
      sigma4PeriodicFirstPositiveSpectralValueRealization hL S hvne hshift hμne hupper

theorem sigma4OpenFirstPositiveSpectralValue_le_of_rowStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt sigma4BlockStarOpenLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ}
    {phase : Offset → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0) :
    sigma4OpenFirstPositiveSpectralValue L ≤ μ := by
  exact BoundarySpectralValueRealizationFrom.le_of_rowStencilEigenmode
    sigma4OpenFirstPositiveSpectralValueRealization hL S hvne hshift hsymbol hμne

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_rowStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt sigma4PeriodicBlockStarLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ}
    {phase : Offset → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤ μ := by
  exact BoundarySpectralValueRealizationFrom.le_of_rowStencilEigenmode
    sigma4PeriodicFirstPositiveSpectralValueRealization hL S hvne hshift hsymbol hμne

theorem sigma4OpenFirstPositiveSpectralValue_rescaled_upper_of_rowStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt sigma4BlockStarOpenLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ}
    {phase : Offset → SigmaCoord4 L → ℝ} {μ coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4OpenFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    BoundarySpectralValueRealizationFrom.rescaled_value_upper_of_rowStencilEigenmode
      sigma4OpenFirstPositiveSpectralValueRealization hL S hvne hshift
      hsymbol hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_rowStencilEigenmode
    {L : ℕ} (hL : 4 ≤ L)
    {Offset : Type*} [Fintype Offset]
    (S : BoundaryRowStencilAt sigma4PeriodicBlockStarLaplacianFamily L Offset)
    {v : SigmaCoord4 L → ℝ}
    {phase : Offset → SigmaCoord4 L → ℝ} {μ coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ δ i, v (S.shift δ i) = phase δ i * v i)
    (hsymbol : ∀ i, S.symbol phase i = μ)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    BoundarySpectralValueRealizationFrom.rescaled_value_upper_of_rowStencilEigenmode
      sigma4PeriodicFirstPositiveSpectralValueRealization hL S hvne hshift
      hsymbol hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_tensorConvolutionSupportSymbol
    {L : ℕ} (hL : 4 ≤ L)
    {v : SigmaCoord4 L → ℝ}
    {phase : SigmaCoord4 L → SigmaCoord4 L → ℝ} {μ : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ j i, v j = phase j i * v i)
    (hsymbol :
      ∀ i,
        1 - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
          (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
            phase j i) = μ)
    (hμne : μ ≠ 0) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤ μ := by
  exact sigma4PeriodicFirstPositiveSpectralValue_le_of_rowStencilEigenmode
    hL (sigma4PeriodicTensorConvolutionRowStencil L) hvne hshift
    (by
      intro i
      rw [sigma4PeriodicTensorConvolutionRowStencil_symbol_eq_support
        L hL phase i]
      exact hsymbol i)
    hμne

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_tensorConvolutionSupportSymbol
    {L : ℕ} (hL : 4 ≤ L)
    {v : SigmaCoord4 L → ℝ}
    {phase : SigmaCoord4 L → SigmaCoord4 L → ℝ}
    {μ coefficient upperError : ℝ}
    (hvne : v ≠ 0)
    (hshift : ∀ j i, v j = phase j i * v i)
    (hsymbol :
      ∀ i,
        1 - (sigmaPeriodicTensorConvolutionSupport4 L i).sum
          (fun j => ((sigmaPeriodicTensorConvolutionKernel4 i j : ℝ) / 256) *
            phase j i) = μ)
    (hμne : μ ≠ 0)
    (hupper : (L : ℝ) ^ 2 * μ ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_rowStencilEigenmode
      hL (sigma4PeriodicTensorConvolutionRowStencil L) hvne hshift
      (by
        intro i
        rw [sigma4PeriodicTensorConvolutionRowStencil_symbol_eq_support
          L hL phase i]
        exact hsymbol i)
      hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_xAxisSecondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) {φ : Fin L → ℝ} {c : ℝ}
    (hvne : sigma4PeriodicXAxisProfile φ ≠ 0)
    (hφ : CoordPeriodicSecondNeighborEigenprofile φ c)
    (hμne : ((1 - c) / 2 : ℝ) ≠ 0) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤ ((1 - c) / 2 : ℝ) := by
  exact sigma4PeriodicFirstPositiveSpectralValue_le_of_eigenmode
    hL hvne
    (sigma4PeriodicXAxisProfile_laplacianMulVec_eq_of_secondNeighborEigenprofile
      L hL φ hφ)
    hμne

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_xAxisSecondNeighborEigenprofile
    {L : ℕ} (hL : 4 ≤ L) {φ : Fin L → ℝ} {c coefficient upperError : ℝ}
    (hvne : sigma4PeriodicXAxisProfile φ ≠ 0)
    (hφ : CoordPeriodicSecondNeighborEigenprofile φ c)
    (hμne : ((1 - c) / 2 : ℝ) ≠ 0)
    (hupper : (L : ℝ) ^ 2 * ((1 - c) / 2 : ℝ) ≤ coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_eigenmode
    hL hvne
    (sigma4PeriodicXAxisProfile_laplacianMulVec_eq_of_secondNeighborEigenprofile
      L hL φ hφ)
    hμne hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_le_of_periodicCosineXAxisProfile
    {L : ℕ} (hL : 4 ≤ L) :
    sigma4PeriodicFirstPositiveSpectralValue L ≤
      ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) := by
  exact sigma4PeriodicFirstPositiveSpectralValue_le_of_xAxisSecondNeighborEigenprofile
    hL
    (sigma4PeriodicCosineXAxisProfile_ne_zero hL)
    (coordPeriodicCosineMode_secondNeighborEigenprofile hL)
    (periodicCosineEigenvalue_ne_zero hL)

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_periodicCosineXAxisProfile
    {L : ℕ} (hL : 4 ≤ L) {coefficient upperError : ℝ}
    (hupper :
      (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ≤
        coefficient + upperError) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      coefficient + upperError := by
  exact
    sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_xAxisSecondNeighborEigenprofile
      hL
      (sigma4PeriodicCosineXAxisProfile_ne_zero hL)
      (coordPeriodicCosineMode_secondNeighborEigenprofile hL)
      (periodicCosineEigenvalue_ne_zero hL)
      hupper

theorem sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_pi_sq_of_periodicCosineXAxisProfile
    {L : ℕ} (hL : 4 ≤ L) :
    (L : ℝ) ^ 2 * sigma4PeriodicFirstPositiveSpectralValue L ≤
      Real.pi ^ 2 := by
  simpa using
    (sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_of_periodicCosineXAxisProfile
      (L := L) (coefficient := Real.pi ^ 2) (upperError := 0) hL
      (by
        simpa using periodicCosineEigenvalue_rescaled_le_pi_sq hL))

/-- One-dimensional lazy Fourier symbol of the closed two-block kernel. -/
noncomputable def sigma4PeriodicCoordinateLazyFourierSymbol
    (L : ℕ) (k : Fin L) : ℝ :=
  (1 + Real.cos (periodicCosineAngle L * (k.val : ℝ))) / 2

/--
Explicit four-dimensional tensor Fourier symbol of the periodic block-star
random-walk Laplacian.
-/
noncomputable def sigma4PeriodicTensorFourierSymbol
    (L : ℕ) (k : SigmaCoord4 L) : ℝ :=
  1 -
    (((sigma4PeriodicCoordinateLazyFourierSymbol L k.1.1.1 *
        sigma4PeriodicCoordinateLazyFourierSymbol L k.1.1.2) *
          sigma4PeriodicCoordinateLazyFourierSymbol L k.1.2) *
            sigma4PeriodicCoordinateLazyFourierSymbol L k.2)

lemma sigma4PeriodicCoordinateLazyFourierSymbol_zero
    {L : ℕ} (hLpos : 0 < L) :
    sigma4PeriodicCoordinateLazyFourierSymbol L ⟨0, hLpos⟩ = 1 := by
  simp [sigma4PeriodicCoordinateLazyFourierSymbol]

lemma sigma4PeriodicTensorFourierSymbol_zero
    {L : ℕ} (hLpos : 0 < L) :
    sigma4PeriodicTensorFourierSymbol L
      ((((⟨0, hLpos⟩, ⟨0, hLpos⟩), ⟨0, hLpos⟩), ⟨0, hLpos⟩)) = 0 := by
  simp [sigma4PeriodicTensorFourierSymbol,
    sigma4PeriodicCoordinateLazyFourierSymbol_zero hLpos]

lemma sigma4PeriodicTensorFourierSymbol_axisOne
    {L : ℕ} (hL : 1 < L) :
    sigma4PeriodicTensorFourierSymbol L
      ((((⟨1, hL⟩, ⟨0, Nat.zero_lt_of_lt hL⟩),
          ⟨0, Nat.zero_lt_of_lt hL⟩),
            ⟨0, Nat.zero_lt_of_lt hL⟩)) =
        ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) := by
  simp [sigma4PeriodicTensorFourierSymbol,
    sigma4PeriodicCoordinateLazyFourierSymbol]
  ring

noncomputable def sigma4PeriodicTensorCosineProfile
    (L : ℕ) (k : SigmaCoord4 L) : SigmaCoord4 L → ℝ :=
  sigma4PeriodicTensorProductProfile
    (coordPeriodicCosineModeFreq L k.1.1.1)
    (coordPeriodicCosineModeFreq L k.1.1.2)
    (coordPeriodicCosineModeFreq L k.1.2)
    (coordPeriodicCosineModeFreq L k.2)

lemma sigma4PeriodicTensorCosineProfile_ne_zero
    {L : ℕ} (hL : 4 ≤ L) (k : SigmaCoord4 L) :
    sigma4PeriodicTensorCosineProfile L k ≠ 0 := by
  intro hzero
  have hLpos : 0 < L := lt_of_lt_of_le (by norm_num : 0 < 4) hL
  let z : Fin L := ⟨0, hLpos⟩
  let i : SigmaCoord4 L := (((z, z), z), z)
  have hval := congrFun hzero i
  simp [sigma4PeriodicTensorCosineProfile, sigma4PeriodicTensorProductProfile,
    coordPeriodicCosineModeFreq, i, z] at hval

theorem sigma4PeriodicTensorCosineProfile_laplacianMulVec_eq
    (L : ℕ) (hL : 4 ≤ L) (k : SigmaCoord4 L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicTensorCosineProfile L k) =
      fun i =>
        sigma4PeriodicTensorFourierSymbol L k *
          sigma4PeriodicTensorCosineProfile L k i := by
  have hx :=
    coordPeriodicCosineModeFreq_secondNeighborEigenprofile hL k.1.1.1
  have hy :=
    coordPeriodicCosineModeFreq_secondNeighborEigenprofile hL k.1.1.2
  have hz :=
    coordPeriodicCosineModeFreq_secondNeighborEigenprofile hL k.1.2
  have ht :=
    coordPeriodicCosineModeFreq_secondNeighborEigenprofile hL k.2
  simpa [sigma4PeriodicTensorCosineProfile, sigma4PeriodicTensorFourierSymbol,
    sigma4PeriodicCoordinateLazyFourierSymbol] using
    (sigma4PeriodicTensorProductProfile_laplacianMulVec_eq_of_secondNeighborEigenprofiles
      L hL
      (coordPeriodicCosineModeFreq L k.1.1.1)
      (coordPeriodicCosineModeFreq L k.1.1.2)
      (coordPeriodicCosineModeFreq L k.1.2)
      (coordPeriodicCosineModeFreq L k.2)
      hx hy hz ht)

abbrev SigmaTrigChoice4 := ((Bool × Bool) × Bool) × Bool

noncomputable def sigma4PeriodicTensorTrigProfile
    (choice : SigmaTrigChoice4) (L : ℕ) (k : SigmaCoord4 L) :
    SigmaCoord4 L → ℝ :=
  sigma4PeriodicTensorProductProfile
    (coordPeriodicTrigModeFreq choice.1.1.1 L k.1.1.1)
    (coordPeriodicTrigModeFreq choice.1.1.2 L k.1.1.2)
    (coordPeriodicTrigModeFreq choice.1.2 L k.1.2)
    (coordPeriodicTrigModeFreq choice.2 L k.2)

theorem sigma4PeriodicTensorTrigProfile_laplacianMulVec_eq
    (L : ℕ) (hL : 4 ≤ L) (choice : SigmaTrigChoice4) (k : SigmaCoord4 L) :
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L
        (sigma4PeriodicTensorTrigProfile choice L k) =
      fun i =>
        sigma4PeriodicTensorFourierSymbol L k *
          sigma4PeriodicTensorTrigProfile choice L k i := by
  have hx :=
    coordPeriodicTrigModeFreq_secondNeighborEigenprofile hL choice.1.1.1 k.1.1.1
  have hy :=
    coordPeriodicTrigModeFreq_secondNeighborEigenprofile hL choice.1.1.2 k.1.1.2
  have hz :=
    coordPeriodicTrigModeFreq_secondNeighborEigenprofile hL choice.1.2 k.1.2
  have ht :=
    coordPeriodicTrigModeFreq_secondNeighborEigenprofile hL choice.2 k.2
  simpa [sigma4PeriodicTensorTrigProfile, sigma4PeriodicTensorFourierSymbol,
    sigma4PeriodicCoordinateLazyFourierSymbol] using
    (sigma4PeriodicTensorProductProfile_laplacianMulVec_eq_of_secondNeighborEigenprofiles
      L hL
      (coordPeriodicTrigModeFreq choice.1.1.1 L k.1.1.1)
      (coordPeriodicTrigModeFreq choice.1.1.2 L k.1.1.2)
      (coordPeriodicTrigModeFreq choice.1.2 L k.1.2)
      (coordPeriodicTrigModeFreq choice.2 L k.2)
      hx hy hz ht)

abbrev SigmaZModCoord4 (L : ℕ) :=
  (((ZMod L × ZMod L) × ZMod L) × ZMod L)

noncomputable def sigmaCoord4ZModEquiv (L : ℕ) [NeZero L] :
    SigmaCoord4 L ≃ SigmaZModCoord4 L where
  toFun i :=
    ((((ZMod.finEquiv L) i.1.1.1,
      (ZMod.finEquiv L) i.1.1.2),
      (ZMod.finEquiv L) i.1.2),
      (ZMod.finEquiv L) i.2)
  invFun z :=
    (((((ZMod.finEquiv L).symm z.1.1.1,
      (ZMod.finEquiv L).symm z.1.1.2),
      (ZMod.finEquiv L).symm z.1.2),
      (ZMod.finEquiv L).symm z.2))
  left_inv i := by
    ext <;> simp
  right_inv z := by
    ext <;> simp

abbrev sigmaZModUnitX (L : ℕ) : SigmaZModCoord4 L := (((1, 0), 0), 0)
abbrev sigmaZModUnitY (L : ℕ) : SigmaZModCoord4 L := (((0, 1), 0), 0)
abbrev sigmaZModUnitZ (L : ℕ) : SigmaZModCoord4 L := (((0, 0), 1), 0)
abbrev sigmaZModUnitT (L : ℕ) : SigmaZModCoord4 L := (((0, 0), 0), 1)

lemma sigmaCoord4ZModEquiv_nextX (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicNextX i) =
      sigmaCoord4ZModEquiv L i + sigmaZModUnitX L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicNextX,
    sigmaZModUnitX, coordPeriodicNext_zmod]

lemma sigmaCoord4ZModEquiv_prevX (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicPrevX i) =
      sigmaCoord4ZModEquiv L i - sigmaZModUnitX L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicPrevX,
    sigmaZModUnitX, coordPeriodicPrev_zmod]

lemma sigmaCoord4ZModEquiv_nextY (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicNextY i) =
      sigmaCoord4ZModEquiv L i + sigmaZModUnitY L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicNextY,
    sigmaZModUnitY, coordPeriodicNext_zmod]

lemma sigmaCoord4ZModEquiv_prevY (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicPrevY i) =
      sigmaCoord4ZModEquiv L i - sigmaZModUnitY L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicPrevY,
    sigmaZModUnitY, coordPeriodicPrev_zmod]

lemma sigmaCoord4ZModEquiv_nextZ (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicNextZ i) =
      sigmaCoord4ZModEquiv L i + sigmaZModUnitZ L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicNextZ,
    sigmaZModUnitZ, coordPeriodicNext_zmod]

lemma sigmaCoord4ZModEquiv_prevZ (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicPrevZ i) =
      sigmaCoord4ZModEquiv L i - sigmaZModUnitZ L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicPrevZ,
    sigmaZModUnitZ, coordPeriodicPrev_zmod]

lemma sigmaCoord4ZModEquiv_nextT (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicNextT i) =
      sigmaCoord4ZModEquiv L i + sigmaZModUnitT L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicNextT,
    sigmaZModUnitT, coordPeriodicNext_zmod]

lemma sigmaCoord4ZModEquiv_prevT (L : ℕ) [NeZero L] (i : SigmaCoord4 L) :
    sigmaCoord4ZModEquiv L (sigmaCoord4PeriodicPrevT i) =
      sigmaCoord4ZModEquiv L i - sigmaZModUnitT L := by
  ext <;> simp [sigmaCoord4ZModEquiv, sigmaCoord4PeriodicPrevT,
    sigmaZModUnitT, coordPeriodicPrev_zmod]

noncomputable def sigmaCoord4ComplexPullback (L : ℕ) [NeZero L] :
    (SigmaZModCoord4 L → ℂ) ≃ₗ[ℂ] (SigmaCoord4 L → ℂ) :=
  (LinearEquiv.piCongrLeft ℂ (fun _ => ℂ) (sigmaCoord4ZModEquiv L)).symm

lemma sigmaCoord4ComplexPullback_apply (L : ℕ) [NeZero L]
    (f : SigmaZModCoord4 L → ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4ComplexPullback L f i = f (sigmaCoord4ZModEquiv L i) := by
  rfl

/--
Mathlib's finite-abelian character basis, transported from `(ZMod L)^ 4`
to the concrete periodic coordinate type used by the Appendix-VI matrix.
-/
noncomputable def sigmaCoord4AddCharComplexBasis (L : ℕ) [NeZero L] :
    Module.Basis (AddChar (SigmaZModCoord4 L) ℂ) ℂ (SigmaCoord4 L → ℂ) :=
  (AddChar.complexBasis (SigmaZModCoord4 L)).map
    (sigmaCoord4ComplexPullback L)

lemma sigmaCoord4AddCharComplexBasis_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ i = ψ (sigmaCoord4ZModEquiv L i) := by
  rw [sigmaCoord4AddCharComplexBasis, Module.Basis.map_apply]
  rw [AddChar.complexBasis_apply]
  exact sigmaCoord4ComplexPullback_apply L ψ i

lemma sigmaCoord4AddCharComplexBasis_nextX_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicNextX i) =
      ψ (sigmaZModUnitX L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_nextX]
  rw [AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_prevX_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicPrevX i) =
      ψ (-sigmaZModUnitX L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_prevX]
  simp [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_nextY_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicNextY i) =
      ψ (sigmaZModUnitY L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_nextY]
  rw [AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_prevY_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicPrevY i) =
      ψ (-sigmaZModUnitY L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_prevY]
  simp [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_nextZ_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicNextZ i) =
      ψ (sigmaZModUnitZ L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_nextZ]
  rw [AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_prevZ_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicPrevZ i) =
      ψ (-sigmaZModUnitZ L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_prevZ]
  simp [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_nextT_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicNextT i) =
      ψ (sigmaZModUnitT L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_nextT]
  rw [AddChar.map_add_eq_mul]
  ring

lemma sigmaCoord4AddCharComplexBasis_prevT_apply (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (i : SigmaCoord4 L) :
    sigmaCoord4AddCharComplexBasis L ψ (sigmaCoord4PeriodicPrevT i) =
      ψ (-sigmaZModUnitT L) * sigmaCoord4AddCharComplexBasis L ψ i := by
  rw [sigmaCoord4AddCharComplexBasis_apply, sigmaCoord4AddCharComplexBasis_apply]
  rw [sigmaCoord4ZModEquiv_prevT]
  simp [sub_eq_add_neg, AddChar.map_add_eq_mul]
  ring

lemma sigmaZModCoord4_axis_decomposition (L : ℕ) (z : SigmaZModCoord4 L) :
    z = (((z.1.1.1, 0), 0), 0) + (((0, z.1.1.2), 0), 0) +
      (((0, 0), z.1.2), 0) + (((0, 0), 0), z.2) := by
  ext <;> simp

noncomputable def sigmaCoord4AddCharAxisProfileX (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L → ℂ :=
  fun x => ψ ((((ZMod.finEquiv L) x, 0), 0), 0)

noncomputable def sigmaCoord4AddCharAxisProfileY (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L → ℂ :=
  fun y => ψ (((0, (ZMod.finEquiv L) y), 0), 0)

noncomputable def sigmaCoord4AddCharAxisProfileZ (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L → ℂ :=
  fun z => ψ (((0, 0), (ZMod.finEquiv L) z), 0)

noncomputable def sigmaCoord4AddCharAxisProfileT (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L → ℂ :=
  fun t => ψ (((0, 0), 0), (ZMod.finEquiv L) t)

lemma sigmaCoord4AddCharComplexBasis_eq_tensorProductProfile (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigmaCoord4AddCharComplexBasis L ψ =
      sigma4PeriodicTensorProductProfileComplex
        (sigmaCoord4AddCharAxisProfileX L ψ)
        (sigmaCoord4AddCharAxisProfileY L ψ)
        (sigmaCoord4AddCharAxisProfileZ L ψ)
        (sigmaCoord4AddCharAxisProfileT L ψ) := by
  ext i
  rw [sigmaCoord4AddCharComplexBasis_apply]
  have hdecomp := sigmaZModCoord4_axis_decomposition L (sigmaCoord4ZModEquiv L i)
  rw [hdecomp]
  rw [AddChar.map_add_eq_mul]
  rw [AddChar.map_add_eq_mul]
  rw [AddChar.map_add_eq_mul]
  simp [sigmaCoord4ZModEquiv, sigma4PeriodicTensorProductProfileComplex,
    sigmaCoord4AddCharAxisProfileX, sigmaCoord4AddCharAxisProfileY,
    sigmaCoord4AddCharAxisProfileZ, sigmaCoord4AddCharAxisProfileT]

lemma sigmaCoord4AddCharAxisProfileX_next (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileX L ψ (coordPeriodicNext a) =
      ψ (sigmaZModUnitX L) * sigmaCoord4AddCharAxisProfileX L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileX, coordPeriodicNext_zmod]
  have haxis : ((((ZMod.finEquiv L) a + 1, 0), 0), 0) =
      sigmaZModUnitX L + ((((ZMod.finEquiv L) a, 0), 0), 0) := by
    ext <;> simp [sigmaZModUnitX, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileX_prev (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileX L ψ (coordPeriodicPrev a) =
      ψ (-sigmaZModUnitX L) * sigmaCoord4AddCharAxisProfileX L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileX, coordPeriodicPrev_zmod]
  have haxis : ((((ZMod.finEquiv L) a - 1, 0), 0), 0) =
      -sigmaZModUnitX L + ((((ZMod.finEquiv L) a, 0), 0), 0) := by
    ext <;> simp [sigmaZModUnitX, sub_eq_add_neg, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileY_next (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileY L ψ (coordPeriodicNext a) =
      ψ (sigmaZModUnitY L) * sigmaCoord4AddCharAxisProfileY L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileY, coordPeriodicNext_zmod]
  have haxis : (((0, (ZMod.finEquiv L) a + 1), 0), 0) =
      sigmaZModUnitY L + (((0, (ZMod.finEquiv L) a), 0), 0) := by
    ext <;> simp [sigmaZModUnitY, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileY_prev (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileY L ψ (coordPeriodicPrev a) =
      ψ (-sigmaZModUnitY L) * sigmaCoord4AddCharAxisProfileY L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileY, coordPeriodicPrev_zmod]
  have haxis : (((0, (ZMod.finEquiv L) a - 1), 0), 0) =
      -sigmaZModUnitY L + (((0, (ZMod.finEquiv L) a), 0), 0) := by
    ext <;> simp [sigmaZModUnitY, sub_eq_add_neg, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileZ_next (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileZ L ψ (coordPeriodicNext a) =
      ψ (sigmaZModUnitZ L) * sigmaCoord4AddCharAxisProfileZ L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileZ, coordPeriodicNext_zmod]
  have haxis : (((0, 0), (ZMod.finEquiv L) a + 1), 0) =
      sigmaZModUnitZ L + (((0, 0), (ZMod.finEquiv L) a), 0) := by
    ext <;> simp [sigmaZModUnitZ, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileZ_prev (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileZ L ψ (coordPeriodicPrev a) =
      ψ (-sigmaZModUnitZ L) * sigmaCoord4AddCharAxisProfileZ L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileZ, coordPeriodicPrev_zmod]
  have haxis : (((0, 0), (ZMod.finEquiv L) a - 1), 0) =
      -sigmaZModUnitZ L + (((0, 0), (ZMod.finEquiv L) a), 0) := by
    ext <;> simp [sigmaZModUnitZ, sub_eq_add_neg, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileT_next (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileT L ψ (coordPeriodicNext a) =
      ψ (sigmaZModUnitT L) * sigmaCoord4AddCharAxisProfileT L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileT, coordPeriodicNext_zmod]
  have haxis : (((0, 0), 0), (ZMod.finEquiv L) a + 1) =
      sigmaZModUnitT L + (((0, 0), 0), (ZMod.finEquiv L) a) := by
    ext <;> simp [sigmaZModUnitT, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileT_prev (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    sigmaCoord4AddCharAxisProfileT L ψ (coordPeriodicPrev a) =
      ψ (-sigmaZModUnitT L) * sigmaCoord4AddCharAxisProfileT L ψ a := by
  simp only [sigmaCoord4AddCharAxisProfileT, coordPeriodicPrev_zmod]
  have haxis : (((0, 0), 0), (ZMod.finEquiv L) a - 1) =
      -sigmaZModUnitT L + (((0, 0), 0), (ZMod.finEquiv L) a) := by
    ext <;> simp [sigmaZModUnitT, sub_eq_add_neg, add_comm]
  rw [haxis, AddChar.map_add_eq_mul]

lemma sigmaCoord4AddCharAxisProfileX_action_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    coordPeriodicClosedTwoBlockConvolutionActionComplex a
        (sigmaCoord4AddCharAxisProfileX L ψ) =
      (2 + ψ (sigmaZModUnitX L) + ψ (-sigmaZModUnitX L)) *
        sigmaCoord4AddCharAxisProfileX L ψ a := by
  rw [coordPeriodicClosedTwoBlockConvolutionActionComplex_eq hL]
  rw [sigmaCoord4AddCharAxisProfileX_next]
  rw [sigmaCoord4AddCharAxisProfileX_prev]
  ring

lemma sigmaCoord4AddCharAxisProfileY_action_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    coordPeriodicClosedTwoBlockConvolutionActionComplex a
        (sigmaCoord4AddCharAxisProfileY L ψ) =
      (2 + ψ (sigmaZModUnitY L) + ψ (-sigmaZModUnitY L)) *
        sigmaCoord4AddCharAxisProfileY L ψ a := by
  rw [coordPeriodicClosedTwoBlockConvolutionActionComplex_eq hL]
  rw [sigmaCoord4AddCharAxisProfileY_next]
  rw [sigmaCoord4AddCharAxisProfileY_prev]
  ring

lemma sigmaCoord4AddCharAxisProfileZ_action_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    coordPeriodicClosedTwoBlockConvolutionActionComplex a
        (sigmaCoord4AddCharAxisProfileZ L ψ) =
      (2 + ψ (sigmaZModUnitZ L) + ψ (-sigmaZModUnitZ L)) *
        sigmaCoord4AddCharAxisProfileZ L ψ a := by
  rw [coordPeriodicClosedTwoBlockConvolutionActionComplex_eq hL]
  rw [sigmaCoord4AddCharAxisProfileZ_next]
  rw [sigmaCoord4AddCharAxisProfileZ_prev]
  ring

lemma sigmaCoord4AddCharAxisProfileT_action_eq {L : ℕ} [NeZero L]
    (hL : 3 ≤ L) (ψ : AddChar (SigmaZModCoord4 L) ℂ) (a : Fin L) :
    coordPeriodicClosedTwoBlockConvolutionActionComplex a
        (sigmaCoord4AddCharAxisProfileT L ψ) =
      (2 + ψ (sigmaZModUnitT L) + ψ (-sigmaZModUnitT L)) *
        sigmaCoord4AddCharAxisProfileT L ψ a := by
  rw [coordPeriodicClosedTwoBlockConvolutionActionComplex_eq hL]
  rw [sigmaCoord4AddCharAxisProfileT_next]
  rw [sigmaCoord4AddCharAxisProfileT_prev]
  ring

noncomputable def sigma4PeriodicAddCharSymbol (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : ℂ :=
  1 - ((((2 + ψ (sigmaZModUnitX L) + ψ (-sigmaZModUnitX L)) *
          (2 + ψ (sigmaZModUnitY L) + ψ (-sigmaZModUnitY L))) *
            (2 + ψ (sigmaZModUnitZ L) + ψ (-sigmaZModUnitZ L))) *
              (2 + ψ (sigmaZModUnitT L) + ψ (-sigmaZModUnitT L))) / 256

theorem sigma4PeriodicBlockStarComplexMulVec_addCharBasis_eq
    (L : ℕ) [NeZero L] (hL : 4 ≤ L)
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    realMatrixComplexMulVecLinearMap
        (sigma4PeriodicBlockStarRandomWalkLaplacian L)
        (sigmaCoord4AddCharComplexBasis L ψ) =
      sigma4PeriodicAddCharSymbol L ψ • sigmaCoord4AddCharComplexBasis L ψ := by
  ext i
  have hL3 : 3 ≤ L := le_trans (by norm_num : 3 ≤ 4) hL
  rw [sigma4PeriodicBlockStarComplexMulVec_eq_tensor_convolutionKernel L hL]
  rw [sigmaCoord4AddCharComplexBasis_eq_tensorProductProfile]
  rw [sigma4PeriodicTensorProductProfileComplex_tensorConvolutionKernel_sum]
  rw [sigmaCoord4AddCharAxisProfileX_action_eq hL3]
  rw [sigmaCoord4AddCharAxisProfileY_action_eq hL3]
  rw [sigmaCoord4AddCharAxisProfileZ_action_eq hL3]
  rw [sigmaCoord4AddCharAxisProfileT_action_eq hL3]
  simp [sigma4PeriodicAddCharSymbol, sigma4PeriodicTensorProductProfileComplex]
  ring

lemma zmod_finEquiv_val {L : ℕ} [NeZero L] (k : Fin L) :
    ((ZMod.finEquiv L) k).val = k.val := by
  cases L with
  | zero => cases NeZero.ne 0 rfl
  | succ N => rfl

lemma zmod_finEquiv_eq_natCast {L : ℕ} [NeZero L] (k : Fin L) :
    ((ZMod.finEquiv L) k) = ((k.val : ℕ) : ZMod L) := by
  rw [← zmod_finEquiv_val (L := L) k]
  exact (ZMod.natCast_zmod_val ((ZMod.finEquiv L) k)).symm

lemma zmod_finEquiv_eq_intCast {L : ℕ} [NeZero L] (k : Fin L) :
    ((ZMod.finEquiv L) k) = ((k.val : ℤ) : ZMod L) := by
  rw [zmod_finEquiv_eq_natCast]
  norm_num

lemma zmodAddEquiv_fin_one_value {L : ℕ} [NeZero L] (k : Fin L) :
    AddChar.zmodAddEquiv ((k.val : ℤ) : ZMod L) (1 : ZMod L) =
      Complex.exp (((2 * Real.pi * ((k.val : ℝ) / (L : ℝ))) : ℂ) * Complex.I) := by
  calc
    AddChar.zmodAddEquiv ((k.val : ℤ) : ZMod L) (1 : ZMod L) =
        ((AddChar.zmod L ((k.val : ℤ) : ZMod L) (1 : ZMod L) : Circle) : ℂ) := by
      simp [AddChar.zmodAddEquiv_apply, AddChar.circleEquivComplex]
    _ =
        ((Circle.exp
          (2 * Real.pi * (((k.val : ℤ) * (1 : ℤ) : ℝ) / (L : ℝ))) :
            Circle) : ℂ) := by
      have h := AddChar.zmod_intCast L (k.val : ℤ) (1 : ℤ)
      simpa using congrArg (fun z : Circle => (z : ℂ)) h
    _ = Complex.exp (((2 * Real.pi * ((k.val : ℝ) / (L : ℝ))) : ℂ) * Complex.I) := by
      rw [Circle.coe_exp]
      norm_num

lemma zmodAddEquiv_finEquiv_one_value {L : ℕ} [NeZero L] (k : Fin L) :
    AddChar.zmodAddEquiv ((ZMod.finEquiv L) k) (1 : ZMod L) =
      Complex.exp (((periodicCosineAngle L * (k.val : ℝ)) : ℂ) * Complex.I) := by
  rw [zmod_finEquiv_eq_intCast]
  rw [zmodAddEquiv_fin_one_value]
  simp [periodicCosineAngle]
  ring_nf

lemma complex_exp_I_add_exp_neg_I (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + Complex.exp ((-θ : ℂ) * Complex.I) =
      (2 * Real.cos θ : ℂ) := by
  rw [Complex.exp_mul_I, Complex.exp_mul_I]
  simp [Complex.ofReal_cos]
  ring

lemma complex_exp_I_inv_eq_exp_neg_I (θ : ℝ) :
    (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ = Complex.exp ((-θ : ℂ) * Complex.I) := by
  rw [← Complex.exp_neg]
  congr 1
  norm_num

lemma complex_exp_I_add_inv (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) + (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      (2 * Real.cos θ : ℂ) := by
  rw [complex_exp_I_inv_eq_exp_neg_I]
  exact complex_exp_I_add_exp_neg_I θ

lemma complex_exp_I_mul_add_inv (θ a : ℝ) :
    Complex.exp ((θ : ℂ) * (a : ℂ) * Complex.I) +
        (Complex.exp ((θ : ℂ) * (a : ℂ) * Complex.I))⁻¹ =
      (2 * Real.cos (θ * a) : ℂ) := by
  rw [show (θ : ℂ) * (a : ℂ) * Complex.I = (((θ * a : ℝ) : ℂ) * Complex.I) by
    norm_num]
  exact complex_exp_I_add_inv (θ * a)

lemma complex_axisFactor_eq_four_lazy (L : ℕ) (k : Fin L) :
    2 + Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I) +
        (Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I))⁻¹ =
      (4 * sigma4PeriodicCoordinateLazyFourierSymbol L k : ℂ) := by
  have h := complex_exp_I_mul_add_inv (periodicCosineAngle L) (k.val : ℝ)
  calc
    2 + Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I) +
        (Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I))⁻¹ =
        2 + (Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I) +
          (Complex.exp (↑(periodicCosineAngle L) * ↑↑↑k * Complex.I))⁻¹) := by
      ring
    _ = 2 + (2 * Real.cos (periodicCosineAngle L * (k.val : ℝ)) : ℂ) := by
      simpa using congrArg (fun z : ℂ => 2 + z) h
    _ = (4 * sigma4PeriodicCoordinateLazyFourierSymbol L k : ℂ) := by
      simp [sigma4PeriodicCoordinateLazyFourierSymbol]
      ring

noncomputable def sigmaCoord4AddCharRestrictX (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : AddChar (ZMod L) ℂ where
  toFun a := ψ ((((a, 0), 0), 0))
  map_zero_eq_one' := by change ψ (0 : SigmaZModCoord4 L) = 1; exact ψ.map_zero_eq_one
  map_add_eq_mul' := by intro a b; rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp

noncomputable def sigmaCoord4AddCharRestrictY (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : AddChar (ZMod L) ℂ where
  toFun a := ψ (((0, a), 0), 0)
  map_zero_eq_one' := by change ψ (0 : SigmaZModCoord4 L) = 1; exact ψ.map_zero_eq_one
  map_add_eq_mul' := by intro a b; rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp

noncomputable def sigmaCoord4AddCharRestrictZ (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : AddChar (ZMod L) ℂ where
  toFun a := ψ (((0, 0), a), 0)
  map_zero_eq_one' := by change ψ (0 : SigmaZModCoord4 L) = 1; exact ψ.map_zero_eq_one
  map_add_eq_mul' := by intro a b; rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp

noncomputable def sigmaCoord4AddCharRestrictT (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : AddChar (ZMod L) ℂ where
  toFun a := ψ (((0, 0), 0), a)
  map_zero_eq_one' := by change ψ (0 : SigmaZModCoord4 L) = 1; exact ψ.map_zero_eq_one
  map_add_eq_mul' := by intro a b; rw [← AddChar.map_add_eq_mul]; congr 1; ext <;> simp

noncomputable def sigmaCoord4AddCharFrequencyX (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L :=
  (ZMod.finEquiv L).symm ((AddChar.zmodAddEquiv).symm (sigmaCoord4AddCharRestrictX L ψ))
noncomputable def sigmaCoord4AddCharFrequencyY (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L :=
  (ZMod.finEquiv L).symm ((AddChar.zmodAddEquiv).symm (sigmaCoord4AddCharRestrictY L ψ))
noncomputable def sigmaCoord4AddCharFrequencyZ (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L :=
  (ZMod.finEquiv L).symm ((AddChar.zmodAddEquiv).symm (sigmaCoord4AddCharRestrictZ L ψ))
noncomputable def sigmaCoord4AddCharFrequencyT (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : Fin L :=
  (ZMod.finEquiv L).symm ((AddChar.zmodAddEquiv).symm (sigmaCoord4AddCharRestrictT L ψ))

lemma sigmaCoord4AddCharRestrictX_eq_zmodAddEquiv (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigmaCoord4AddCharRestrictX L ψ =
      AddChar.zmodAddEquiv ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyX L ψ)) := by
  simp [sigmaCoord4AddCharFrequencyX]
lemma sigmaCoord4AddCharRestrictY_eq_zmodAddEquiv (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigmaCoord4AddCharRestrictY L ψ =
      AddChar.zmodAddEquiv ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyY L ψ)) := by
  simp [sigmaCoord4AddCharFrequencyY]
lemma sigmaCoord4AddCharRestrictZ_eq_zmodAddEquiv (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigmaCoord4AddCharRestrictZ L ψ =
      AddChar.zmodAddEquiv ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyZ L ψ)) := by
  simp [sigmaCoord4AddCharFrequencyZ]
lemma sigmaCoord4AddCharRestrictT_eq_zmodAddEquiv (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigmaCoord4AddCharRestrictT L ψ =
      AddChar.zmodAddEquiv ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyT L ψ)) := by
  simp [sigmaCoord4AddCharFrequencyT]

lemma sigmaCoord4AddCharRestrictX_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (sigmaZModUnitX L) =
      AddChar.zmodAddEquiv
        ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyX L ψ)) (1 : ZMod L) := by
  rw [← sigmaCoord4AddCharRestrictX_eq_zmodAddEquiv]; rfl
lemma sigmaCoord4AddCharRestrictY_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (sigmaZModUnitY L) =
      AddChar.zmodAddEquiv
        ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyY L ψ)) (1 : ZMod L) := by
  rw [← sigmaCoord4AddCharRestrictY_eq_zmodAddEquiv]; rfl
lemma sigmaCoord4AddCharRestrictZ_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (sigmaZModUnitZ L) =
      AddChar.zmodAddEquiv
        ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyZ L ψ)) (1 : ZMod L) := by
  rw [← sigmaCoord4AddCharRestrictZ_eq_zmodAddEquiv]; rfl
lemma sigmaCoord4AddCharRestrictT_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (sigmaZModUnitT L) =
      AddChar.zmodAddEquiv
        ((ZMod.finEquiv L) (sigmaCoord4AddCharFrequencyT L ψ)) (1 : ZMod L) := by
  rw [← sigmaCoord4AddCharRestrictT_eq_zmodAddEquiv]; rfl

lemma sigmaCoord4AddCharRestrictX_neg_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (-sigmaZModUnitX L) = (ψ (sigmaZModUnitX L))⁻¹ := by rw [← AddChar.map_neg_eq_inv]
lemma sigmaCoord4AddCharRestrictY_neg_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (-sigmaZModUnitY L) = (ψ (sigmaZModUnitY L))⁻¹ := by rw [← AddChar.map_neg_eq_inv]
lemma sigmaCoord4AddCharRestrictZ_neg_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (-sigmaZModUnitZ L) = (ψ (sigmaZModUnitZ L))⁻¹ := by rw [← AddChar.map_neg_eq_inv]
lemma sigmaCoord4AddCharRestrictT_neg_one (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    ψ (-sigmaZModUnitT L) = (ψ (sigmaZModUnitT L))⁻¹ := by rw [← AddChar.map_neg_eq_inv]

lemma sigmaCoord4AddCharAxisFactorX_eq_four_lazy (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    2 + ψ (sigmaZModUnitX L) + ψ (-sigmaZModUnitX L) =
      (4 *
        sigma4PeriodicCoordinateLazyFourierSymbol L
          (sigmaCoord4AddCharFrequencyX L ψ) : ℂ) := by
  rw [sigmaCoord4AddCharRestrictX_neg_one, sigmaCoord4AddCharRestrictX_one]
  rw [zmodAddEquiv_finEquiv_one_value]
  exact complex_axisFactor_eq_four_lazy L (sigmaCoord4AddCharFrequencyX L ψ)

lemma sigmaCoord4AddCharAxisFactorY_eq_four_lazy (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    2 + ψ (sigmaZModUnitY L) + ψ (-sigmaZModUnitY L) =
      (4 *
        sigma4PeriodicCoordinateLazyFourierSymbol L
          (sigmaCoord4AddCharFrequencyY L ψ) : ℂ) := by
  rw [sigmaCoord4AddCharRestrictY_neg_one, sigmaCoord4AddCharRestrictY_one]
  rw [zmodAddEquiv_finEquiv_one_value]
  exact complex_axisFactor_eq_four_lazy L (sigmaCoord4AddCharFrequencyY L ψ)

lemma sigmaCoord4AddCharAxisFactorZ_eq_four_lazy (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    2 + ψ (sigmaZModUnitZ L) + ψ (-sigmaZModUnitZ L) =
      (4 *
        sigma4PeriodicCoordinateLazyFourierSymbol L
          (sigmaCoord4AddCharFrequencyZ L ψ) : ℂ) := by
  rw [sigmaCoord4AddCharRestrictZ_neg_one, sigmaCoord4AddCharRestrictZ_one]
  rw [zmodAddEquiv_finEquiv_one_value]
  exact complex_axisFactor_eq_four_lazy L (sigmaCoord4AddCharFrequencyZ L ψ)

lemma sigmaCoord4AddCharAxisFactorT_eq_four_lazy (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    2 + ψ (sigmaZModUnitT L) + ψ (-sigmaZModUnitT L) =
      (4 *
        sigma4PeriodicCoordinateLazyFourierSymbol L
          (sigmaCoord4AddCharFrequencyT L ψ) : ℂ) := by
  rw [sigmaCoord4AddCharRestrictT_neg_one, sigmaCoord4AddCharRestrictT_one]
  rw [zmodAddEquiv_finEquiv_one_value]
  exact complex_axisFactor_eq_four_lazy L (sigmaCoord4AddCharFrequencyT L ψ)

noncomputable def sigmaCoord4AddCharFrequency4 (L : ℕ) [NeZero L]
    (ψ : AddChar (SigmaZModCoord4 L) ℂ) : SigmaCoord4 L :=
  (((sigmaCoord4AddCharFrequencyX L ψ, sigmaCoord4AddCharFrequencyY L ψ),
      sigmaCoord4AddCharFrequencyZ L ψ), sigmaCoord4AddCharFrequencyT L ψ)

theorem sigma4PeriodicAddCharSymbol_eq_tensorFourierSymbol_complex
    (L : ℕ) [NeZero L] (ψ : AddChar (SigmaZModCoord4 L) ℂ) :
    sigma4PeriodicAddCharSymbol L ψ =
      (sigma4PeriodicTensorFourierSymbol L (sigmaCoord4AddCharFrequency4 L ψ) : ℂ) := by
  rw [sigma4PeriodicAddCharSymbol]
  rw [sigmaCoord4AddCharAxisFactorX_eq_four_lazy]
  rw [sigmaCoord4AddCharAxisFactorY_eq_four_lazy]
  rw [sigmaCoord4AddCharAxisFactorZ_eq_four_lazy]
  rw [sigmaCoord4AddCharAxisFactorT_eq_four_lazy]
  simp [sigma4PeriodicTensorFourierSymbol, sigmaCoord4AddCharFrequency4]
  ring

theorem sigma4PeriodicHermitianEigenvalue_eq_addCharSymbol_complex
    (L : ℕ) [NeZero L] (hL : 4 ≤ L)
    (hA : (sigma4PeriodicBlockStarRandomWalkLaplacian L).IsHermitian)
    (idx : SigmaCoord4 L) :
    ∃ ψ : AddChar (SigmaZModCoord4 L) ℂ,
      sigma4PeriodicAddCharSymbol L ψ = (hA.eigenvalues idx : ℂ) := by
  let A := sigma4PeriodicBlockStarRandomWalkLaplacian L
  let B := sigmaCoord4AddCharComplexBasis L
  let T := realMatrixComplexMulVecLinearMap A
  let lam : AddChar (SigmaZModCoord4 L) ℂ → ℂ := sigma4PeriodicAddCharSymbol L
  let vR : SigmaCoord4 L → ℝ := (hA.eigenvectorBasis idx).ofLp
  let vC : SigmaCoord4 L → ℂ := fun i => (vR i : ℂ)
  have hdiag : ∀ ψ : AddChar (SigmaZModCoord4 L) ℂ, T (B ψ) = lam ψ • B ψ := by
    intro ψ
    exact sigma4PeriodicBlockStarComplexMulVec_addCharBasis_eq L hL ψ
  have hvR : A.mulVec vR = hA.eigenvalues idx • vR := by
    simpa [A, vR] using hA.mulVec_eigenvectorBasis idx
  have hvC : T vC = (hA.eigenvalues idx : ℂ) • vC := by
    rw [show T vC = realMatrixComplexMulVecLinearMap A (fun i => (vR i : ℂ)) by rfl]
    rw [realMatrixComplexMulVecLinearMap_ofReal]
    ext i
    have hpoint := congrFun hvR i
    change ((A.mulVec vR i : ℝ) : ℂ) = (hA.eigenvalues idx : ℂ) * (vR i : ℂ)
    rw [hpoint]
    simp [Pi.smul_apply]
  have hvne : vC ≠ 0 := by
    intro hzero
    have hvRzero : vR = 0 := by
      ext i
      have h := congrFun hzero i
      exact Complex.ofReal_injective h
    have hbne : hA.eigenvectorBasis idx ≠ 0 :=
      (hA.eigenvectorBasis.orthonormal.ne_zero idx)
    apply hbne
    apply (WithLp.ofLp_injective 2)
    simpa [vR] using hvRzero
  exact eigenvalue_mem_range_of_eigenbasis B T lam hdiag hvC hvne



theorem sigma4PeriodicTensorFourierSymbol_mem_spectralSet
    (L : ℕ) (hL : 4 ≤ L) (k : SigmaCoord4 L) :
    sigma4PeriodicTensorFourierSymbol L k ∈
      sigma4PeriodicBlockStarLaplacianFamily.spectralSet L := by
  exact sigma4PeriodicBlockStarLaplacianFamily.mem_spectralSet_of_eigenmode
    L
    (sigma4PeriodicTensorCosineProfile_ne_zero hL k)
    (sigma4PeriodicTensorCosineProfile_laplacianMulVec_eq L hL k)

lemma sigma4PeriodicCoordinateLazyFourierSymbol_nonneg
    (L : ℕ) (k : Fin L) :
    0 ≤ sigma4PeriodicCoordinateLazyFourierSymbol L k := by
  have hcos := Real.neg_one_le_cos
    (periodicCosineAngle L * (k.val : ℝ))
  simp [sigma4PeriodicCoordinateLazyFourierSymbol]
  nlinarith

lemma sigma4PeriodicCoordinateLazyFourierSymbol_le_one
    (L : ℕ) (k : Fin L) :
    sigma4PeriodicCoordinateLazyFourierSymbol L k ≤ 1 := by
  have hcos := Real.cos_le_one
    (periodicCosineAngle L * (k.val : ℝ))
  simp [sigma4PeriodicCoordinateLazyFourierSymbol]
  nlinarith

private lemma periodicCosineAngle_mul_le_pi_of_two_mul_le
    {L m : ℕ} (hL : 4 ≤ L) (hm : 2 * m ≤ L) :
    periodicCosineAngle L * (m : ℝ) ≤ Real.pi := by
  have hLpos : 0 < L := by omega
  have hθL : periodicCosineAngle L * (L : ℝ) = 2 * Real.pi :=
    periodicCosineAngle_mul_nat hLpos
  have hθnonneg : 0 ≤ periodicCosineAngle L :=
    le_of_lt (periodicCosineAngle_pos hL)
  have hmreal : (2 : ℝ) * (m : ℝ) ≤ (L : ℝ) := by
    exact_mod_cast hm
  have hmreal' : (m : ℝ) ≤ (L : ℝ) / 2 := by
    linarith
  have hmul := mul_le_mul_of_nonneg_left hmreal' hθnonneg
  have hcalc : periodicCosineAngle L * ((L : ℝ) / 2) = Real.pi := by
    nlinarith
  nlinarith

private lemma periodicCosineAngle_le_mul_of_one_le
    {L m : ℕ} (hL : 4 ≤ L) (hm : 1 ≤ m) :
    periodicCosineAngle L ≤ periodicCosineAngle L * (m : ℝ) := by
  have hθnonneg : 0 ≤ periodicCosineAngle L :=
    le_of_lt (periodicCosineAngle_pos hL)
  have hmreal : (1 : ℝ) ≤ (m : ℝ) := by
    exact_mod_cast hm
  have hmul := mul_le_mul_of_nonneg_left hmreal hθnonneg
  simpa using hmul

private lemma periodicCosineAngle_cos_mul_eq_cos_sub
    {L k : ℕ} (hL : 4 ≤ L) (hk : k < L) :
    Real.cos (periodicCosineAngle L * (k : ℝ)) =
      Real.cos (periodicCosineAngle L * ((L - k : ℕ) : ℝ)) := by
  have hLpos : 0 < L := by omega
  have hθL : periodicCosineAngle L * (L : ℝ) = 2 * Real.pi :=
    periodicCosineAngle_mul_nat hLpos
  have hsub : ((L - k : ℕ) : ℝ) = (L : ℝ) - (k : ℝ) :=
    Nat.cast_sub (Nat.le_of_lt hk)
  have harg :
      periodicCosineAngle L * (k : ℝ) =
        2 * Real.pi -
          periodicCosineAngle L * ((L - k : ℕ) : ℝ) := by
    rw [hsub]
    nlinarith
  rw [harg, Real.cos_two_pi_sub]

private lemma sigmaFourProduct_le_first {a b c d : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd1 : d ≤ 1) :
    (((a * b) * c) * d) ≤ a := by
  have hbc_nonneg : 0 ≤ b * c := mul_nonneg hb0 hc0
  have hbcd_le_bc : (b * c) * d ≤ b * c :=
    mul_le_of_le_one_right hbc_nonneg hd1
  have hbc_le_b : b * c ≤ b := mul_le_of_le_one_right hb0 hc1
  have hbcd_le_b : (b * c) * d ≤ b := le_trans hbcd_le_bc hbc_le_b
  have hbcd_le_one : (b * c) * d ≤ 1 := le_trans hbcd_le_b hb1
  calc
    (((a * b) * c) * d) = a * ((b * c) * d) := by ring
    _ ≤ a := mul_le_of_le_one_right ha0 hbcd_le_one

private lemma sigmaFourProduct_le_second {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd1 : d ≤ 1) :
    (((a * b) * c) * d) ≤ b := by
  have hac_nonneg : 0 ≤ a * c := mul_nonneg ha0 hc0
  have hacd_le_ac : (a * c) * d ≤ a * c :=
    mul_le_of_le_one_right hac_nonneg hd1
  have hac_le_a : a * c ≤ a := mul_le_of_le_one_right ha0 hc1
  have hacd_le_a : (a * c) * d ≤ a := le_trans hacd_le_ac hac_le_a
  have hacd_le_one : (a * c) * d ≤ 1 := le_trans hacd_le_a ha1
  calc
    (((a * b) * c) * d) = b * ((a * c) * d) := by ring
    _ ≤ b := mul_le_of_le_one_right hb0 hacd_le_one

private lemma sigmaFourProduct_le_third {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hd1 : d ≤ 1) :
    (((a * b) * c) * d) ≤ c := by
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha0 hb0
  have habd_le_ab : (a * b) * d ≤ a * b :=
    mul_le_of_le_one_right hab_nonneg hd1
  have hab_le_a : a * b ≤ a := mul_le_of_le_one_right ha0 hb1
  have habd_le_a : (a * b) * d ≤ a := le_trans habd_le_ab hab_le_a
  have habd_le_one : (a * b) * d ≤ 1 := le_trans habd_le_a ha1
  calc
    (((a * b) * c) * d) = c * ((a * b) * d) := by ring
    _ ≤ c := mul_le_of_le_one_right hc0 habd_le_one

private lemma sigmaFourProduct_le_fourth {a b c d : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) :
    (((a * b) * c) * d) ≤ d := by
  have hab_nonneg : 0 ≤ a * b := mul_nonneg ha0 hb0
  have habc_le_ab : (a * b) * c ≤ a * b :=
    mul_le_of_le_one_right hab_nonneg hc1
  have hab_le_a : a * b ≤ a := mul_le_of_le_one_right ha0 hb1
  have habc_le_a : (a * b) * c ≤ a := le_trans habc_le_ab hab_le_a
  have habc_le_one : (a * b) * c ≤ 1 := le_trans habc_le_a ha1
  calc
    (((a * b) * c) * d) = d * ((a * b) * c) := by ring
    _ ≤ d := mul_le_of_le_one_right hd0 habc_le_one

private lemma sigmaFourProduct_le_of_one_factor_le {a b c d z : ℝ}
    (ha0 : 0 ≤ a) (ha1 : a ≤ 1) (hb0 : 0 ≤ b) (hb1 : b ≤ 1)
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hd0 : 0 ≤ d) (hd1 : d ≤ 1)
    (hsmall : a ≤ z ∨ b ≤ z ∨ c ≤ z ∨ d ≤ z) :
    (((a * b) * c) * d) ≤ z := by
  rcases hsmall with haz | hbz | hcz | hdz
  · exact le_trans
      (sigmaFourProduct_le_first ha0 hb0 hb1 hc0 hc1 hd1) haz
  · exact le_trans
      (sigmaFourProduct_le_second ha0 ha1 hb0 hc0 hc1 hd1) hbz
  · exact le_trans
      (sigmaFourProduct_le_third ha0 ha1 hb0 hb1 hc0 hd1) hcz
  · exact le_trans
      (sigmaFourProduct_le_fourth ha0 ha1 hb0 hb1 hc0 hc1 hd0) hdz

def Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap : Prop :=
  ∀ L, 4 ≤ L → ∀ k : Fin L,
    sigma4PeriodicCoordinateLazyFourierSymbol L k ≠ 1 →
      sigma4PeriodicCoordinateLazyFourierSymbol L k ≤
        ((1 + Real.cos (periodicCosineAngle L)) / 2 : ℝ)

def Sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc : Prop :=
  ∀ L, 4 ≤ L → ∀ k : Fin L,
    sigma4PeriodicCoordinateLazyFourierSymbol L k ≠ 1 →
      ∃ θ : ℝ,
        Real.cos (periodicCosineAngle L * (k.val : ℝ)) = Real.cos θ ∧
          periodicCosineAngle L ≤ θ ∧ θ ≤ Real.pi

theorem sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc :
    Sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc := by
  intro L hL k hk
  have hklt : k.val < L := k.isLt
  have hkne : k.val ≠ 0 := by
    intro hzero
    apply hk
    simp [sigma4PeriodicCoordinateLazyFourierSymbol, hzero]
  by_cases hlow : k.val ≤ L / 2
  · refine ⟨periodicCosineAngle L * (k.val : ℝ), ?_, ?_, ?_⟩
    · rfl
    · have hge : 1 ≤ k.val :=
        Nat.succ_le_iff.mpr (Nat.pos_of_ne_zero hkne)
      exact periodicCosineAngle_le_mul_of_one_le hL hge
    · have h2 : 2 * k.val ≤ L := by omega
      exact periodicCosineAngle_mul_le_pi_of_two_mul_le hL h2
  · refine
      ⟨periodicCosineAngle L * ((L - k.val : ℕ) : ℝ), ?_, ?_, ?_⟩
    · exact periodicCosineAngle_cos_mul_eq_cos_sub hL hklt
    · have hge : 1 ≤ L - k.val := by omega
      exact periodicCosineAngle_le_mul_of_one_le hL hge
    · have h2 : 2 * (L - k.val) ≤ L := by omega
      exact periodicCosineAngle_mul_le_pi_of_two_mul_le hL h2

theorem Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap.of_frequencyFold
    (hfold : Sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc) :
    Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap := by
  intro L hL k hk
  rcases hfold L hL k hk with ⟨θ, hcos, hθlo, hθhi⟩
  have hangle_nonneg : 0 ≤ periodicCosineAngle L :=
    le_of_lt (periodicCosineAngle_pos hL)
  have hcos_le :
      Real.cos θ ≤ Real.cos (periodicCosineAngle L) :=
    Real.cos_le_cos_of_nonneg_of_le_pi hangle_nonneg hθhi hθlo
  simp [sigma4PeriodicCoordinateLazyFourierSymbol, hcos]
  nlinarith

def Sigma4PeriodicCoordinateLazyFourierSymbolGap : Prop :=
  ∀ L, 4 ≤ L → ∀ k : Fin L,
    let s := sigma4PeriodicCoordinateLazyFourierSymbol L k
    0 ≤ s ∧ s ≤ 1 ∧
      (s ≠ 1 →
        s ≤ ((1 + Real.cos (periodicCosineAngle L)) / 2 : ℝ))

theorem Sigma4PeriodicCoordinateLazyFourierSymbolGap.of_maximalGap
    (hmax : Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap) :
    Sigma4PeriodicCoordinateLazyFourierSymbolGap := by
  intro L hL k
  exact ⟨
    sigma4PeriodicCoordinateLazyFourierSymbol_nonneg L k,
    sigma4PeriodicCoordinateLazyFourierSymbol_le_one L k,
    hmax L hL k⟩

def Sigma4PeriodicTensorFourierSpectrumCoverage : Prop :=
  ∀ L, 4 ≤ L → ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L,
    ∃ k : SigmaCoord4 L, sigma4PeriodicTensorFourierSymbol L k = μ

/--
Concrete remaining diagonalization condition for the periodic Appendix-VI
operator: every Mathlib Hermitian eigenvalue of the finite block-star matrix is
one of the tensor Fourier symbols.
-/
def Sigma4PeriodicHermitianEigenvalueFourierCoverage : Prop :=
  ∀ L, 4 ≤ L →
    ∀ hA : (sigma4PeriodicBlockStarRandomWalkLaplacian L).IsHermitian,
      ∀ i : SigmaCoord4 L,
        ∃ k : SigmaCoord4 L, sigma4PeriodicTensorFourierSymbol L k = hA.eigenvalues i

theorem sigma4PeriodicHermitianEigenvalueFourierCoverage :
    Sigma4PeriodicHermitianEigenvalueFourierCoverage := by
  intro L hL hA idx
  letI : NeZero L := ⟨by omega⟩
  rcases sigma4PeriodicHermitianEigenvalue_eq_addCharSymbol_complex L hL hA idx with
    ⟨ψ, hψ⟩
  refine ⟨sigmaCoord4AddCharFrequency4 L ψ, ?_⟩
  apply Complex.ofReal_injective
  calc
    (sigma4PeriodicTensorFourierSymbol L (sigmaCoord4AddCharFrequency4 L ψ) : ℂ) =
        sigma4PeriodicAddCharSymbol L ψ := by
      rw [sigma4PeriodicAddCharSymbol_eq_tensorFourierSymbol_complex]
    _ = (hA.eigenvalues idx : ℂ) := hψ


theorem Sigma4PeriodicTensorFourierSpectrumCoverage.of_hermitianEigenvalueFourierCoverage
    (hcover : Sigma4PeriodicHermitianEigenvalueFourierCoverage) :
    Sigma4PeriodicTensorFourierSpectrumCoverage := by
  intro L hL μ hμ
  let hA := sigma4PeriodicBlockStarRandomWalkLaplacian_isHermitian L hL
  have hμspec : μ ∈ spectrum ℝ (sigma4PeriodicBlockStarRandomWalkLaplacian L) := by
    simpa [BoundaryLaplacianFamily.spectralSet, sigma4PeriodicBlockStarLaplacianFamily] using hμ
  have hμrange : μ ∈ Set.range hA.eigenvalues := by
    rwa [hA.spectrum_real_eq_range_eigenvalues] at hμspec
  rcases hμrange with ⟨i, hi⟩
  rcases hcover L hL hA i with ⟨k, hk⟩
  exact ⟨k, hk.trans hi⟩

theorem sigma4PeriodicTensorFourierSpectrumCoverage :
    Sigma4PeriodicTensorFourierSpectrumCoverage :=
  Sigma4PeriodicTensorFourierSpectrumCoverage.of_hermitianEigenvalueFourierCoverage
    sigma4PeriodicHermitianEigenvalueFourierCoverage


def Sigma4PeriodicTensorFourierSymbolGap : Prop :=
  ∀ L, 4 ≤ L → ∀ k : SigmaCoord4 L,
    sigma4PeriodicTensorFourierSymbol L k ≠ 0 →
      ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ≤
        sigma4PeriodicTensorFourierSymbol L k

theorem Sigma4PeriodicTensorFourierSymbolGap.of_coordinateGap
    (hcoord : Sigma4PeriodicCoordinateLazyFourierSymbolGap) :
    Sigma4PeriodicTensorFourierSymbolGap := by
  intro L hL k hne
  let a : ℝ := sigma4PeriodicCoordinateLazyFourierSymbol L k.1.1.1
  let b : ℝ := sigma4PeriodicCoordinateLazyFourierSymbol L k.1.1.2
  let c : ℝ := sigma4PeriodicCoordinateLazyFourierSymbol L k.1.2
  let d : ℝ := sigma4PeriodicCoordinateLazyFourierSymbol L k.2
  let z : ℝ := ((1 + Real.cos (periodicCosineAngle L)) / 2 : ℝ)
  have ha : 0 ≤ a ∧ a ≤ 1 ∧ (a ≠ 1 → a ≤ z) := by
    simpa [a, z] using hcoord L hL k.1.1.1
  have hb : 0 ≤ b ∧ b ≤ 1 ∧ (b ≠ 1 → b ≤ z) := by
    simpa [b, z] using hcoord L hL k.1.1.2
  have hc : 0 ≤ c ∧ c ≤ 1 ∧ (c ≠ 1 → c ≤ z) := by
    simpa [c, z] using hcoord L hL k.1.2
  have hd : 0 ≤ d ∧ d ≤ 1 ∧ (d ≠ 1 → d ≤ z) := by
    simpa [d, z] using hcoord L hL k.2
  rcases ha with ⟨ha0, ha1, hagap⟩
  rcases hb with ⟨hb0, hb1, hbgap⟩
  rcases hc with ⟨hc0, hc1, hcgap⟩
  rcases hd with ⟨hd0, hd1, hdgap⟩
  have hsomeSmall : a ≤ z ∨ b ≤ z ∨ c ≤ z ∨ d ≤ z := by
    by_cases haeq : a = 1
    · by_cases hbeq : b = 1
      · by_cases hceq : c = 1
        · by_cases hdeq : d = 1
          · exfalso
            apply hne
            simp [sigma4PeriodicTensorFourierSymbol, a, b, c, d,
              haeq, hbeq, hceq, hdeq]
          · exact Or.inr (Or.inr (Or.inr (hdgap hdeq)))
        · exact Or.inr (Or.inr (Or.inl (hcgap hceq)))
      · exact Or.inr (Or.inl (hbgap hbeq))
    · exact Or.inl (hagap haeq)
  have hprod_le_z :
      (((a * b) * c) * d) ≤ z :=
    sigmaFourProduct_le_of_one_factor_le
      ha0 ha1 hb0 hb1 hc0 hc1 hd0 hd1 hsomeSmall
  have htarget :
      ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) = 1 - z := by
    simp [z]
    ring
  rw [htarget]
  have hle : 1 - z ≤ 1 - (((a * b) * c) * d) :=
    sub_le_sub_left hprod_le_z 1
  simpa [sigma4PeriodicTensorFourierSymbol, a, b, c, d] using hle

/--
Exact finite periodic spectral gap for the tensor-convolution block-star
Laplacian.  It states that the one-axis cosine eigenvalue is the bottom of the
non-zero spectrum at each finite periodic scale.
-/
def Sigma4PeriodicExactCosineSpectralGap : Prop :=
  ∀ L, 4 ≤ L → ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L,
    μ ≠ 0 →
      ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) ≤ μ

theorem Sigma4PeriodicExactCosineSpectralGap.of_tensorFourier
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage)
    (hgap : Sigma4PeriodicTensorFourierSymbolGap) :
    Sigma4PeriodicExactCosineSpectralGap := by
  intro L hL μ hμmem hμne
  rcases hcover L hL μ hμmem with ⟨k, hk⟩
  have hsym_ne : sigma4PeriodicTensorFourierSymbol L k ≠ 0 := by
    rw [hk]
    exact hμne
  simpa [hk] using hgap L hL k hsym_ne

theorem Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierAndCoordinateMaximalGap
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage)
    (hmax : Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap) :
    Sigma4PeriodicExactCosineSpectralGap :=
  Sigma4PeriodicExactCosineSpectralGap.of_tensorFourier hcover
    (Sigma4PeriodicTensorFourierSymbolGap.of_coordinateGap
      (Sigma4PeriodicCoordinateLazyFourierSymbolGap.of_maximalGap hmax))

theorem Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierAndFrequencyFold
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage)
    (hfold : Sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc) :
    Sigma4PeriodicExactCosineSpectralGap :=
  Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierAndCoordinateMaximalGap
    hcover
    (Sigma4PeriodicCoordinateLazyFourierSymbolMaximalGap.of_frequencyFold
      hfold)

theorem Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage) :
    Sigma4PeriodicExactCosineSpectralGap :=
  Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierAndFrequencyFold
    hcover
    sigma4PeriodicCoordinateFrequencyFoldToFundamentalArc

theorem sigma4PeriodicExactCosineSpectralGap :
    Sigma4PeriodicExactCosineSpectralGap :=
  Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
    sigma4PeriodicTensorFourierSpectrumCoverage

noncomputable def sigma4PeriodicRescaledLowerCertificate_pi_sq_of_exactCosineSpectralGap
    (hgap : Sigma4PeriodicExactCosineSpectralGap) :
    BoundaryRescaledSpectralLowerCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4 where
  L0_pos := by norm_num
  lowerError := fun L =>
    Real.pi ^ 2 -
      (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ)
  lowerError_tendsto_zero := by
    have h :
        Filter.Tendsto
          (fun L : ℕ =>
            Real.pi ^ 2 -
              (L : ℝ) ^ 2 * ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ))
          Filter.atTop (nhds (Real.pi ^ 2 - Real.pi ^ 2)) :=
      (tendsto_const_nhds.sub periodicCosineEigenvalue_rescaled_tendsto_pi_sq)
    simpa using h
  spectral_lower := by
    intro L hL μ hμmem hμne
    have hμlower := hgap L hL μ hμmem hμne
    have hmul :=
      mul_le_mul_of_nonneg_left hμlower (sq_nonneg (L : ℝ))
    calc
      Real.pi ^ 2 -
          (Real.pi ^ 2 -
            (L : ℝ) ^ 2 *
              ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ))
          =
            (L : ℝ) ^ 2 *
              ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ) := by ring
      _ ≤ (L : ℝ) ^ 2 * μ := hmul

noncomputable def sigma4PeriodicRescaledLowerCertificate_pi_sq_of_tensorFourierSpectrumCoverage
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage) :
    BoundaryRescaledSpectralLowerCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4 :=
  sigma4PeriodicRescaledLowerCertificate_pi_sq_of_exactCosineSpectralGap
    (Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
      hcover)

noncomputable def sigma4PeriodicRescaledLowerCertificate_pi_sq :
    BoundaryRescaledSpectralLowerCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4 :=
  sigma4PeriodicRescaledLowerCertificate_pi_sq_of_tensorFourierSpectrumCoverage
    sigma4PeriodicTensorFourierSpectrumCoverage

theorem sigma4PeriodicRescaledLimitCoefficient_le_pi_sq
    {coefficient : ℝ}
    (hlim :
      Filter.Tendsto
        (fun L : ℕ =>
          rescaledSpectralValue sigma4PeriodicFirstPositiveSpectralValue L)
        Filter.atTop (nhds coefficient)) :
    coefficient ≤ Real.pi ^ 2 := by
  refine le_of_tendsto hlim ?_
  exact Filter.eventually_atTop.mpr ⟨4, by
    intro L hL
    exact
      sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_pi_sq_of_periodicCosineXAxisProfile
        hL⟩

theorem sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_lowerCertificate
    (C :
      BoundaryRescaledSpectralLowerCertificateAt
        sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4) :
    Filter.Tendsto
      (fun L : ℕ =>
        rescaledSpectralValue sigma4PeriodicFirstPositiveSpectralValue L)
      Filter.atTop (nhds (Real.pi ^ 2)) := by
  have hg :
      Filter.Tendsto (fun L : ℕ => Real.pi ^ 2 - C.lowerError L)
        Filter.atTop (nhds (Real.pi ^ 2)) := by
    simpa using (tendsto_const_nhds.sub C.lowerError_tendsto_zero)
  have hh :
      Filter.Tendsto (fun _ : ℕ => Real.pi ^ 2)
        Filter.atTop (nhds (Real.pi ^ 2)) :=
    tendsto_const_nhds
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hg hh ?_ ?_
  · exact Filter.eventually_atTop.mpr ⟨4, by
      intro L hL
      have hmem :=
        sigma4PeriodicFirstPositiveSpectralValueRealization.value_mem L hL
      have hpos :=
        sigma4PeriodicFirstPositiveSpectralValueRealization.value_pos L hL
      have hne : sigma4PeriodicFirstPositiveSpectralValue L ≠ 0 :=
        ne_of_gt hpos
      have hlower := C.spectral_lower L hL
        (sigma4PeriodicFirstPositiveSpectralValue L) hmem hne
      simpa [rescaledSpectralValue] using hlower⟩
  · exact Filter.eventually_atTop.mpr ⟨4, by
      intro L hL
      simpa [rescaledSpectralValue] using
        sigma4PeriodicFirstPositiveSpectralValue_rescaled_upper_pi_sq_of_periodicCosineXAxisProfile
          hL⟩

theorem sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_exactCosineSpectralGap
    (hgap : Sigma4PeriodicExactCosineSpectralGap) :
    Filter.Tendsto
      (fun L : ℕ =>
        rescaledSpectralValue sigma4PeriodicFirstPositiveSpectralValue L)
      Filter.atTop (nhds (Real.pi ^ 2)) :=
  sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_lowerCertificate
    (sigma4PeriodicRescaledLowerCertificate_pi_sq_of_exactCosineSpectralGap hgap)

theorem
  sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_tensorFourierSpectrumCoverage
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage) :
    Filter.Tendsto
      (fun L : ℕ =>
        rescaledSpectralValue sigma4PeriodicFirstPositiveSpectralValue L)
      Filter.atTop (nhds (Real.pi ^ 2)) :=
  sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_exactCosineSpectralGap
    (Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
      hcover)

theorem sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq :
    Filter.Tendsto
      (fun L : ℕ =>
        rescaledSpectralValue sigma4PeriodicFirstPositiveSpectralValue L)
      Filter.atTop (nhds (Real.pi ^ 2)) :=
  sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_tensorFourierSpectrumCoverage
    sigma4PeriodicTensorFourierSpectrumCoverage

noncomputable def sigma4PeriodicRescaledLimitCertificate_pi_sq_of_lowerCertificate
    (C :
      BoundaryRescaledSpectralLowerCertificateAt
        sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4) :
    RescaledInverseSquareLimitCertificate
      sigma4PeriodicFirstPositiveSpectralValue where
  coefficient := Real.pi ^ 2
  coefficient_pos := by positivity
  tendsto_rescaled :=
    sigma4PeriodicFirstPositiveSpectralValue_tendsto_rescaled_pi_sq_of_lowerCertificate
      C

noncomputable def sigma4PeriodicRescaledLimitCertificate_pi_sq_of_exactCosineSpectralGap
    (hgap : Sigma4PeriodicExactCosineSpectralGap) :
    RescaledInverseSquareLimitCertificate
      sigma4PeriodicFirstPositiveSpectralValue :=
  sigma4PeriodicRescaledLimitCertificate_pi_sq_of_lowerCertificate
    (sigma4PeriodicRescaledLowerCertificate_pi_sq_of_exactCosineSpectralGap hgap)

noncomputable def sigma4PeriodicRescaledLimitCertificate_pi_sq_of_tensorFourierSpectrumCoverage
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage) :
    RescaledInverseSquareLimitCertificate
      sigma4PeriodicFirstPositiveSpectralValue :=
  sigma4PeriodicRescaledLimitCertificate_pi_sq_of_exactCosineSpectralGap
    (Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
      hcover)

noncomputable def sigma4PeriodicRescaledLimitCertificate_pi_sq :
    RescaledInverseSquareLimitCertificate
      sigma4PeriodicFirstPositiveSpectralValue :=
  sigma4PeriodicRescaledLimitCertificate_pi_sq_of_tensorFourierSpectrumCoverage
    sigma4PeriodicTensorFourierSpectrumCoverage

noncomputable def sigma4PeriodicCosineUpperWitnessCertificate :
    BoundaryEigenmodeUpperWitnessCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4 where
  L0_pos := by norm_num
  upperError := fun _ => 0
  upperError_tendsto_zero := by
    simp
  eigenvalue := fun L => ((1 - Real.cos (periodicCosineAngle L)) / 2 : ℝ)
  eigenmode := fun L => sigma4PeriodicXAxisProfile (coordPeriodicCosineMode L)
  eigenmode_ne_zero := by
    intro L hL
    exact sigma4PeriodicCosineXAxisProfile_ne_zero hL
  eigenmode_eq := by
    intro L hL
    exact sigma4PeriodicCosineXAxisProfile_laplacianMulVec_eq L hL
  eigenvalue_ne_zero := by
    intro L hL
    exact periodicCosineEigenvalue_ne_zero hL
  eigenvalue_upper := by
    intro L hL
    simpa using periodicCosineEigenvalue_rescaled_le_pi_sq hL

noncomputable def sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_lowerCertificate
    (C :
      BoundaryRescaledSpectralLowerCertificateAt
        sigma4PeriodicBlockStarLaplacianFamily (Real.pi ^ 2) 4) :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      (Real.pi ^ 2) where
  L0 := 4
  realization := sigma4PeriodicFirstPositiveSpectralValueRealization
  lower := C
  upper := sigma4PeriodicCosineUpperWitnessCertificate

noncomputable def
  sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_exactCosineSpectralGap
    (hgap : Sigma4PeriodicExactCosineSpectralGap) :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      (Real.pi ^ 2) :=
  sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_lowerCertificate
    (sigma4PeriodicRescaledLowerCertificate_pi_sq_of_exactCosineSpectralGap hgap)

noncomputable def
  sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_tensorFourierSpectrumCoverage
    (hcover : Sigma4PeriodicTensorFourierSpectrumCoverage) :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      (Real.pi ^ 2) :=
  sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_exactCosineSpectralGap
    (Sigma4PeriodicExactCosineSpectralGap.of_tensorFourierSpectrumCoverage
      hcover)

noncomputable def sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      (Real.pi ^ 2) :=
  sigma4PeriodicSplitEigenmodeRescaledSpectralBracketing_pi_sq_of_tensorFourierSpectrumCoverage
    sigma4PeriodicTensorFourierSpectrumCoverage

noncomputable def sigma4OpenFullRowStencil (L : ℕ) :
    BoundaryRowStencilAt sigma4BlockStarOpenLaplacianFamily L (SigmaCoord4 L) :=
  sigma4BlockStarOpenLaplacianFamily.fullRowStencil L

noncomputable def sigma4PeriodicFullRowStencil (L : ℕ) :
    BoundaryRowStencilAt sigma4PeriodicBlockStarLaplacianFamily L (SigmaCoord4 L) :=
  sigma4PeriodicBlockStarLaplacianFamily.fullRowStencil L

theorem sigma4OpenFullRowStencil_weight_eq_zero_of_disjoint_supports
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hji : j ≠ i)
    (hdisj :
      Disjoint ((sigma4BlockStarCovering L hL).fineEdgeSupport i)
        ((sigma4BlockStarCovering L hL).fineEdgeSupport j)) :
    (sigma4OpenFullRowStencil L).weight i j = 0 := by
  have hS :
      coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4BlockStarCovering L hL).fineEdgeSupport) i j = 0 :=
    coarseOverlapMatrix_fromSupports_eq_zero_of_disjoint
      (sigma4BlockStarCovering L hL).fineEdgeSupport hdisj
  have hA : sigma4BlockStarOpenLaplacianFamily.laplacian L i j = 0 := by
    change sigma4BlockStarRandomWalkLaplacian L i j = 0
    rw [sigma4BlockStarRandomWalkLaplacian_of_four_le L hL]
    exact randomWalkLaplacian_offdiag_eq_zero_of_weight_zero _
      (fun hij => hji hij.symm) hS
  simpa [sigma4OpenFullRowStencil] using
    BoundaryLaplacianFamily.fullRowStencil_weight_eq_zero_of_laplacian_entry_zero
      sigma4BlockStarOpenLaplacianFamily L hji hA

theorem sigma4PeriodicFullRowStencil_weight_eq_zero_of_disjoint_supports
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hji : j ≠ i)
    (hdisj :
      Disjoint ((sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport i)
        ((sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport j)) :
    (sigma4PeriodicFullRowStencil L).weight i j = 0 := by
  have hS :
      coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport) i j = 0 :=
    coarseOverlapMatrix_fromSupports_eq_zero_of_disjoint
      (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport hdisj
  have hA : sigma4PeriodicBlockStarLaplacianFamily.laplacian L i j = 0 := by
    change sigma4PeriodicBlockStarRandomWalkLaplacian L i j = 0
    rw [sigma4PeriodicBlockStarRandomWalkLaplacian_of_four_le L hL]
    exact randomWalkLaplacian_offdiag_eq_zero_of_weight_zero _
      (fun hij => hji hij.symm) hS
  simpa [sigma4PeriodicFullRowStencil] using
    BoundaryLaplacianFamily.fullRowStencil_weight_eq_zero_of_laplacian_entry_zero
      sigma4PeriodicBlockStarLaplacianFamily L hji hA

theorem sigma4OpenFullRowStencil_nonzero_weight_supports_inter_nonempty
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hji : j ≠ i)
    (hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0) :
    (((sigma4BlockStarCovering L hL).fineEdgeSupport i) ∩
        ((sigma4BlockStarCovering L hL).fineEdgeSupport j)).Nonempty := by
  by_contra hno
  apply hw
  exact sigma4OpenFullRowStencil_weight_eq_zero_of_disjoint_supports L hL hji
    (by
      rw [Finset.disjoint_left]
      intro e hi hj
      exact hno ⟨e, by simp [Finset.mem_inter, hi, hj]⟩)

theorem sigma4PeriodicFullRowStencil_nonzero_weight_supports_inter_nonempty
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hji : j ≠ i)
    (hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0) :
    (((sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport i) ∩
        ((sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport j)).Nonempty := by
  by_contra hno
  apply hw
  exact sigma4PeriodicFullRowStencil_weight_eq_zero_of_disjoint_supports L hL hji
    (by
      rw [Finset.disjoint_left]
      intro e hi hj
      exact hno ⟨e, by simp [Finset.mem_inter, hi, hj]⟩)

theorem sigma4OpenFullRowStencil_nonzero_weight_adj_blockSupportOverlapGraph
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0) :
    (blockSupportOverlapGraph
      (sigma4BlockStarCovering L hL).fineEdgeSupport).Adj i j := by
  exact ⟨hij,
    sigma4OpenFullRowStencil_nonzero_weight_supports_inter_nonempty L hL
      (fun hji => hij hji.symm) hw⟩

theorem sigma4PeriodicFullRowStencil_nonzero_weight_adj_blockSupportOverlapGraph
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0) :
    (blockSupportOverlapGraph
      (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport).Adj i j := by
  exact ⟨hij,
    sigma4PeriodicFullRowStencil_nonzero_weight_supports_inter_nonempty L hL
      (fun hji => hij hji.symm) hw⟩

def coordInPathOneStepClosure {L : ℕ} (c d : Fin L) : Prop :=
  c = d ∨ (SimpleGraph.pathGraph L).Adj c d

def cubeCoordInPathOneStepBox {L : ℕ} (c d : CubeCoord L) : Prop :=
  coordInPathOneStepClosure c.1.1 d.1.1 ∧
    coordInPathOneStepClosure c.1.2 d.1.2 ∧
      coordInPathOneStepClosure c.2 d.2

def sigmaCoord4InPathOneStepBox {L : ℕ} (c d : SigmaCoord4 L) : Prop :=
  cubeCoordInPathOneStepBox c.1 d.1 ∧
    coordInPathOneStepClosure c.2 d.2

def coordInCycleOneStepClosure {L : ℕ} (c d : Fin L) : Prop :=
  c = d ∨ (finCycleGraph L).Adj c d

def cubeCoordInCycleOneStepBox {L : ℕ} (c d : CubeCoord L) : Prop :=
  coordInCycleOneStepClosure c.1.1 d.1.1 ∧
    coordInCycleOneStepClosure c.1.2 d.1.2 ∧
      coordInCycleOneStepClosure c.2 d.2

def sigmaCoord4InCycleOneStepBox {L : ℕ} (c d : SigmaCoord4 L) : Prop :=
  cubeCoordInCycleOneStepBox c.1 d.1 ∧
    coordInCycleOneStepClosure c.2 d.2

lemma coordInClosedTwoBlock_common_pathOneStep
    {L : ℕ} {a c d : Fin L}
    (hac : coordInClosedTwoBlock a c)
    (had : coordInClosedTwoBlock a d) :
    coordInPathOneStepClosure c d := by
  rcases hac with hac | hac <;> rcases had with had | had
  · exact Or.inl (hac.symm.trans had)
  · exact Or.inr (by
      rw [SimpleGraph.pathGraph_adj]
      exact Or.inr (by simpa [hac] using had))
  · exact Or.inr (by
      rw [SimpleGraph.pathGraph_adj]
      exact Or.inl (by simpa [had] using hac))
  · exact Or.inl (by
      apply Fin.ext
      have hsucc : c.val + 1 = d.val + 1 := hac.trans had.symm
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hsucc))

lemma cubeCoordInClosedTwoByTwoByTwoStar_common_pathOneStepBox
    {L : ℕ} {a c d : CubeCoord L}
    (hac : cubeCoordInClosedTwoByTwoByTwoStar a c)
    (had : cubeCoordInClosedTwoByTwoByTwoStar a d) :
    cubeCoordInPathOneStepBox c d := by
  exact ⟨
    coordInClosedTwoBlock_common_pathOneStep hac.1 had.1,
    coordInClosedTwoBlock_common_pathOneStep hac.2.1 had.2.1,
    coordInClosedTwoBlock_common_pathOneStep hac.2.2 had.2.2⟩

lemma sigmaCoordInClosedTwoByTwoByTwoByTwoStar_common_pathOneStepBox
    {L : ℕ} {a c d : SigmaCoord4 L}
    (hac : sigmaCoordInClosedTwoByTwoByTwoByTwoStar a c)
    (had : sigmaCoordInClosedTwoByTwoByTwoByTwoStar a d) :
    sigmaCoord4InPathOneStepBox c d := by
  exact ⟨
    cubeCoordInClosedTwoByTwoByTwoStar_common_pathOneStepBox hac.1 had.1,
    coordInClosedTwoBlock_common_pathOneStep hac.2 had.2⟩

lemma coordInPeriodicClosedTwoBlock_common_cycleOneStep
    {L : ℕ} (hL : 2 ≤ L) {a c d : Fin L}
    (hac : coordInPeriodicClosedTwoBlock a c)
    (had : coordInPeriodicClosedTwoBlock a d) :
    coordInCycleOneStepClosure c d := by
  rcases hac with hac | hac | hac <;> rcases had with had | had | had
  · exact Or.inl (hac.symm.trans had)
  · exact Or.inr ((pathGraph_le_finCycleGraph L) (by
      rw [SimpleGraph.pathGraph_adj]
      exact Or.inr (by simpa [hac] using had)))
  · have hc0 : c.val = 0 := by simpa [hac] using had.2
    have hne : c ≠ d := by
      intro hcd
      have hd0 : d.val = 0 := by simpa [hcd] using hc0
      omega
    exact Or.inr ⟨hne, Or.inr (Or.inl ⟨hc0, had.1⟩)⟩
  · exact Or.inr ((pathGraph_le_finCycleGraph L) (by
      rw [SimpleGraph.pathGraph_adj]
      exact Or.inl (by simpa [had] using hac)))
  · exact Or.inl (by
      apply Fin.ext
      have hsucc : c.val + 1 = d.val + 1 := hac.trans had.symm
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hsucc))
  · exfalso
    omega
  · have hd0 : d.val = 0 := by simpa [had] using hac.2
    have hne : c ≠ d := by
      intro hcd
      have hc0 : c.val = 0 := by simpa [hcd] using hd0
      omega
    exact Or.inr ⟨hne, Or.inr (Or.inr ⟨hd0, hac.1⟩)⟩
  · exfalso
    omega
  · exact Or.inl (by
      apply Fin.ext
      have hsucc : c.val + 1 = d.val + 1 := hac.1.trans had.1.symm
      exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hsucc))

lemma cubeCoordInPeriodicTwoByTwoByTwoStar_common_cycleOneStepBox
    {L : ℕ} (hL : 2 ≤ L) {a c d : CubeCoord L}
    (hac : cubeCoordInPeriodicTwoByTwoByTwoStar a c)
    (had : cubeCoordInPeriodicTwoByTwoByTwoStar a d) :
    cubeCoordInCycleOneStepBox c d := by
  exact ⟨
    coordInPeriodicClosedTwoBlock_common_cycleOneStep hL hac.1 had.1,
    coordInPeriodicClosedTwoBlock_common_cycleOneStep hL hac.2.1 had.2.1,
    coordInPeriodicClosedTwoBlock_common_cycleOneStep hL hac.2.2 had.2.2⟩

lemma sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar_common_cycleOneStepBox
    {L : ℕ} (hL : 2 ≤ L) {a c d : SigmaCoord4 L}
    (hac : sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a c)
    (had : sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a d) :
    sigmaCoord4InCycleOneStepBox c d := by
  exact ⟨
    cubeCoordInPeriodicTwoByTwoByTwoStar_common_cycleOneStepBox hL hac.1 had.1,
    coordInPeriodicClosedTwoBlock_common_cycleOneStep hL hac.2 had.2⟩

theorem sigma4Open_blockSupportOverlapGraph_adj_common_closed_star
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hadj :
      (blockSupportOverlapGraph
        (sigma4BlockStarCovering L hL).fineEdgeSupport).Adj i j) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInClosedTwoByTwoByTwoByTwoStar a i ∧
        sigmaCoordInClosedTwoByTwoByTwoByTwoStar a j := by
  rcases hadj.2 with ⟨e, he⟩
  have hi :
      e ∈ (sigma4BlockStarCovering L hL).fineEdgeSupport i :=
    (Finset.mem_inter.mp he).1
  have hj :
      e ∈ (sigma4BlockStarCovering L hL).fineEdgeSupport j :=
    (Finset.mem_inter.mp he).2
  refine ⟨sigmaFineEdgeSource e, ?_, ?_⟩
  · simpa [sigma4BlockStarCovering, sigmaBlockStarSupport4] using hi
  · simpa [sigma4BlockStarCovering, sigmaBlockStarSupport4] using hj

theorem sigma4Periodic_blockSupportOverlapGraph_adj_common_periodic_star
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hadj :
      (blockSupportOverlapGraph
        (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport).Adj i j) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a i ∧
        sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a j := by
  rcases hadj.2 with ⟨e, he⟩
  have hi :
      e ∈ (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport i :=
    (Finset.mem_inter.mp he).1
  have hj :
      e ∈ (sigma4PeriodicBlockStarCovering L hL).fineEdgeSupport j :=
    (Finset.mem_inter.mp he).2
  refine ⟨e.1, ?_, ?_⟩
  · simpa [sigma4PeriodicBlockStarCovering, sigmaPeriodicBlockStarSupport4] using hi
  · simpa [sigma4PeriodicBlockStarCovering, sigmaPeriodicBlockStarSupport4] using hj

theorem sigma4OpenFullRowStencil_nonzero_weight_common_closed_star
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInClosedTwoByTwoByTwoByTwoStar a i ∧
        sigmaCoordInClosedTwoByTwoByTwoByTwoStar a j := by
  exact sigma4Open_blockSupportOverlapGraph_adj_common_closed_star L hL
    (sigma4OpenFullRowStencil_nonzero_weight_adj_blockSupportOverlapGraph
      L hL hij hw)

theorem sigma4PeriodicFullRowStencil_nonzero_weight_common_periodic_star
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0) :
    ∃ a : SigmaCoord4 L,
      sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a i ∧
        sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar a j := by
  exact sigma4Periodic_blockSupportOverlapGraph_adj_common_periodic_star L hL
    (sigma4PeriodicFullRowStencil_nonzero_weight_adj_blockSupportOverlapGraph
      L hL hij hw)

theorem sigma4OpenFullRowStencil_nonzero_weight_pathOneStepBox
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0) :
    sigmaCoord4InPathOneStepBox i j := by
  rcases sigma4OpenFullRowStencil_nonzero_weight_common_closed_star
      L hL hij hw with ⟨a, hai, haj⟩
  exact sigmaCoordInClosedTwoByTwoByTwoByTwoStar_common_pathOneStepBox
    hai haj

theorem sigma4PeriodicFullRowStencil_nonzero_weight_cycleOneStepBox
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hij : i ≠ j)
    (hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0) :
    sigmaCoord4InCycleOneStepBox i j := by
  have hL2 : 2 ≤ L := le_trans (by norm_num : 2 ≤ 4) hL
  rcases sigma4PeriodicFullRowStencil_nonzero_weight_common_periodic_star
      L hL hij hw with ⟨a, hai, haj⟩
  exact sigmaCoordInPeriodicTwoByTwoByTwoByTwoStar_common_cycleOneStepBox
    hL2 hai haj

noncomputable def coordPathOneStepNeighborSet
    (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d => coordInPathOneStepClosure c d

noncomputable def coordPathPrevSet (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d => d.val + 1 = c.val

noncomputable def coordPathNextSet (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d => c.val + 1 = d.val

lemma coordPathPrevSet_card_le_one (L : ℕ) (c : Fin L) :
    (coordPathPrevSet L c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  apply Fin.ext
  have hxv : x.val + 1 = c.val := by
    simpa [coordPathPrevSet] using (Finset.mem_filter.mp hx).2
  have hyv : y.val + 1 = c.val := by
    simpa [coordPathPrevSet] using (Finset.mem_filter.mp hy).2
  exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxv.trans hyv.symm)

lemma coordPathNextSet_card_le_one (L : ℕ) (c : Fin L) :
    (coordPathNextSet L c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  apply Fin.ext
  have hxv : c.val + 1 = x.val := by
    simpa [coordPathNextSet] using (Finset.mem_filter.mp hx).2
  have hyv : c.val + 1 = y.val := by
    simpa [coordPathNextSet] using (Finset.mem_filter.mp hy).2
  exact hxv.symm.trans hyv

lemma coordPathOneStepNeighborSet_subset_three
    (L : ℕ) (c : Fin L) :
    coordPathOneStepNeighborSet L c ⊆
      ({c} ∪ coordPathPrevSet L c ∪ coordPathNextSet L c) := by
  classical
  intro d hd
  have hrel : coordInPathOneStepClosure c d := by
    simpa [coordPathOneStepNeighborSet] using (Finset.mem_filter.mp hd).2
  rcases hrel with hsame | hadj
  · subst hsame
    simp
  · rw [SimpleGraph.pathGraph_adj] at hadj
    rcases hadj with hnext | hprev
    · simp [coordPathNextSet, hnext]
    · simp [coordPathPrevSet, hprev]

lemma coordPathOneStepNeighborSet_card_le_three
    (L : ℕ) (c : Fin L) :
    (coordPathOneStepNeighborSet L c).card ≤ 3 := by
  classical
  let s0 : Finset (Fin L) := {c}
  let sp := coordPathPrevSet L c
  let sn := coordPathNextSet L c
  have hsub : coordPathOneStepNeighborSet L c ⊆ s0 ∪ sp ∪ sn := by
    simpa [s0, sp, sn] using coordPathOneStepNeighborSet_subset_three L c
  have hcard := Finset.card_le_card hsub
  have hprev : sp.card ≤ 1 := by simpa [sp] using coordPathPrevSet_card_le_one L c
  have hnext : sn.card ≤ 1 := by simpa [sn] using coordPathNextSet_card_le_one L c
  have hsing : s0.card = 1 := by simp [s0]
  have hcup1 : (s0 ∪ sp).card ≤ 2 := by
    have hraw := Finset.card_union_le s0 sp
    omega
  have hcup2 : (s0 ∪ sp ∪ sn).card ≤ 3 := by
    have hraw := Finset.card_union_le (s0 ∪ sp) sn
    omega
  exact hcard.trans hcup2

noncomputable def coordCycleOneStepNeighborSet
    (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d => coordInCycleOneStepClosure c d

noncomputable def coordCyclePrevSet (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d =>
    d.val + 1 = c.val ∨ (c.val = 0 ∧ d.val + 1 = L)

noncomputable def coordCycleNextSet (L : ℕ) (c : Fin L) : Finset (Fin L) := by
  classical
  exact Finset.univ.filter fun d =>
    c.val + 1 = d.val ∨ (d.val = 0 ∧ c.val + 1 = L)

lemma coordCyclePrevSet_card_le_one (L : ℕ) (c : Fin L) :
    (coordCyclePrevSet L c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  apply Fin.ext
  have hxv :
      x.val + 1 = c.val ∨ (c.val = 0 ∧ x.val + 1 = L) := by
    simpa [coordCyclePrevSet] using (Finset.mem_filter.mp hx).2
  have hyv :
      y.val + 1 = c.val ∨ (c.val = 0 ∧ y.val + 1 = L) := by
    simpa [coordCyclePrevSet] using (Finset.mem_filter.mp hy).2
  rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv
  · exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxv.trans hyv.symm)
  · omega
  · omega
  · exact Nat.succ.inj (by simpa [Nat.succ_eq_add_one] using hxv.2.trans hyv.2.symm)

lemma coordCycleNextSet_card_le_one (L : ℕ) (c : Fin L) :
    (coordCycleNextSet L c).card ≤ 1 := by
  classical
  rw [Finset.card_le_one]
  intro x hx y hy
  apply Fin.ext
  have hxv :
      c.val + 1 = x.val ∨ (x.val = 0 ∧ c.val + 1 = L) := by
    simpa [coordCycleNextSet] using (Finset.mem_filter.mp hx).2
  have hyv :
      c.val + 1 = y.val ∨ (y.val = 0 ∧ c.val + 1 = L) := by
    simpa [coordCycleNextSet] using (Finset.mem_filter.mp hy).2
  rcases hxv with hxv | hxv <;> rcases hyv with hyv | hyv
  · exact hxv.symm.trans hyv
  · omega
  · omega
  · exact hxv.1.trans hyv.1.symm

lemma coordCycleOneStepNeighborSet_subset_three
    (L : ℕ) (c : Fin L) :
    coordCycleOneStepNeighborSet L c ⊆
      ({c} ∪ coordCyclePrevSet L c ∪ coordCycleNextSet L c) := by
  classical
  intro d hd
  have hrel : coordInCycleOneStepClosure c d := by
    simpa [coordCycleOneStepNeighborSet] using (Finset.mem_filter.mp hd).2
  rcases hrel with hsame | hadj
  · subst hsame
    simp
  · rcases hadj with ⟨_, hcases⟩
    rcases hcases with hpath | hwrap | hwrap
    · rw [SimpleGraph.pathGraph_adj] at hpath
      rcases hpath with hnext | hprev
      · simp [coordCycleNextSet, hnext]
      · simp [coordCyclePrevSet, hprev]
    · simp [coordCyclePrevSet, hwrap]
    · simp [coordCycleNextSet, hwrap]

lemma coordCycleOneStepNeighborSet_card_le_three
    (L : ℕ) (c : Fin L) :
    (coordCycleOneStepNeighborSet L c).card ≤ 3 := by
  classical
  let s0 : Finset (Fin L) := {c}
  let sp := coordCyclePrevSet L c
  let sn := coordCycleNextSet L c
  have hsub : coordCycleOneStepNeighborSet L c ⊆ s0 ∪ sp ∪ sn := by
    simpa [s0, sp, sn] using coordCycleOneStepNeighborSet_subset_three L c
  have hcard := Finset.card_le_card hsub
  have hprev : sp.card ≤ 1 := by simpa [sp] using coordCyclePrevSet_card_le_one L c
  have hnext : sn.card ≤ 1 := by simpa [sn] using coordCycleNextSet_card_le_one L c
  have hsing : s0.card = 1 := by simp [s0]
  have hcup1 : (s0 ∪ sp).card ≤ 2 := by
    have hraw := Finset.card_union_le s0 sp
    omega
  have hcup2 : (s0 ∪ sp ∪ sn).card ≤ 3 := by
    have hraw := Finset.card_union_le (s0 ∪ sp) sn
    omega
  exact hcard.trans hcup2

noncomputable def sigma4PathOneStepBoxSet
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact (((coordPathOneStepNeighborSet L i.1.1.1 ×ˢ
      coordPathOneStepNeighborSet L i.1.1.2) ×ˢ
        coordPathOneStepNeighborSet L i.1.2) ×ˢ
          coordPathOneStepNeighborSet L i.2)

noncomputable def sigma4CycleOneStepBoxSet
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact (((coordCycleOneStepNeighborSet L i.1.1.1 ×ˢ
      coordCycleOneStepNeighborSet L i.1.1.2) ×ˢ
        coordCycleOneStepNeighborSet L i.1.2) ×ˢ
          coordCycleOneStepNeighborSet L i.2)

noncomputable def sigma4OpenOneStepNeighborSet
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact Finset.univ.filter fun j => sigmaCoord4InPathOneStepBox i j

noncomputable def sigma4PeriodicOneStepNeighborSet
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact Finset.univ.filter fun j => sigmaCoord4InCycleOneStepBox i j

theorem sigma4OpenOneStepNeighborSet_subset_pathBoxSet
    (L : ℕ) (i : SigmaCoord4 L) :
    sigma4OpenOneStepNeighborSet L i ⊆ sigma4PathOneStepBoxSet L i := by
  classical
  intro j hj
  have hbox : sigmaCoord4InPathOneStepBox i j := by
    simpa [sigma4OpenOneStepNeighborSet] using (Finset.mem_filter.mp hj).2
  rcases hbox with ⟨hcube, ht⟩
  rcases hcube with ⟨hx, hy, hz⟩
  simp [sigma4PathOneStepBoxSet, coordPathOneStepNeighborSet, hx, hy, hz, ht]

theorem sigma4PeriodicOneStepNeighborSet_subset_cycleBoxSet
    (L : ℕ) (i : SigmaCoord4 L) :
    sigma4PeriodicOneStepNeighborSet L i ⊆ sigma4CycleOneStepBoxSet L i := by
  classical
  intro j hj
  have hbox : sigmaCoord4InCycleOneStepBox i j := by
    simpa [sigma4PeriodicOneStepNeighborSet] using (Finset.mem_filter.mp hj).2
  rcases hbox with ⟨hcube, ht⟩
  rcases hcube with ⟨hx, hy, hz⟩
  simp [sigma4CycleOneStepBoxSet, coordCycleOneStepNeighborSet, hx, hy, hz, ht]

theorem sigma4PathOneStepBoxSet_card_le_eighty_one
    (L : ℕ) (i : SigmaCoord4 L) :
    (sigma4PathOneStepBoxSet L i).card ≤ 81 := by
  classical
  have hx := coordPathOneStepNeighborSet_card_le_three L i.1.1.1
  have hy := coordPathOneStepNeighborSet_card_le_three L i.1.1.2
  have hz := coordPathOneStepNeighborSet_card_le_three L i.1.2
  have ht := coordPathOneStepNeighborSet_card_le_three L i.2
  dsimp [sigma4PathOneStepBoxSet]
  rw [Finset.card_product, Finset.card_product, Finset.card_product]
  have hxy := Nat.mul_le_mul hx hy
  have hxyz := Nat.mul_le_mul hxy hz
  have hxyzt := Nat.mul_le_mul hxyz ht
  norm_num at hxyzt
  simpa [mul_assoc] using hxyzt

theorem sigma4CycleOneStepBoxSet_card_le_eighty_one
    (L : ℕ) (i : SigmaCoord4 L) :
    (sigma4CycleOneStepBoxSet L i).card ≤ 81 := by
  classical
  have hx := coordCycleOneStepNeighborSet_card_le_three L i.1.1.1
  have hy := coordCycleOneStepNeighborSet_card_le_three L i.1.1.2
  have hz := coordCycleOneStepNeighborSet_card_le_three L i.1.2
  have ht := coordCycleOneStepNeighborSet_card_le_three L i.2
  dsimp [sigma4CycleOneStepBoxSet]
  rw [Finset.card_product, Finset.card_product, Finset.card_product]
  have hxy := Nat.mul_le_mul hx hy
  have hxyz := Nat.mul_le_mul hxy hz
  have hxyzt := Nat.mul_le_mul hxyz ht
  norm_num at hxyzt
  simpa [mul_assoc] using hxyzt

theorem sigma4OpenOneStepNeighborSet_card_le_eighty_one
    (L : ℕ) (i : SigmaCoord4 L) :
    (sigma4OpenOneStepNeighborSet L i).card ≤ 81 := by
  exact (Finset.card_le_card (sigma4OpenOneStepNeighborSet_subset_pathBoxSet L i)).trans
    (sigma4PathOneStepBoxSet_card_le_eighty_one L i)

theorem sigma4PeriodicOneStepNeighborSet_card_le_eighty_one
    (L : ℕ) (i : SigmaCoord4 L) :
    (sigma4PeriodicOneStepNeighborSet L i).card ≤ 81 := by
  exact (Finset.card_le_card
    (sigma4PeriodicOneStepNeighborSet_subset_cycleBoxSet L i)).trans
      (sigma4CycleOneStepBoxSet_card_le_eighty_one L i)

noncomputable def sigma4OpenFullRowStencilActiveTargets
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact Finset.univ.filter fun j => (sigma4OpenFullRowStencil L).weight i j ≠ 0

noncomputable def sigma4PeriodicFullRowStencilActiveTargets
    (L : ℕ) (i : SigmaCoord4 L) : Finset (SigmaCoord4 L) := by
  classical
  exact Finset.univ.filter fun j => (sigma4PeriodicFullRowStencil L).weight i j ≠ 0

theorem sigma4OpenFullRowStencil_nonzero_weight_mem_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0) :
    j ∈ sigma4OpenOneStepNeighborSet L i := by
  classical
  by_cases hij : i = j
  · subst hij
    have hzero : (sigma4OpenFullRowStencil L).weight i i = 0 := by
      simpa [sigma4OpenFullRowStencil] using
        BoundaryLaplacianFamily.fullRowStencil_weight_self
          sigma4BlockStarOpenLaplacianFamily L i
    exact False.elim (hw hzero)
  · have hbox :=
      sigma4OpenFullRowStencil_nonzero_weight_pathOneStepBox L hL hij hw
    simp [sigma4OpenOneStepNeighborSet, hbox]

theorem sigma4PeriodicFullRowStencil_nonzero_weight_mem_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0) :
    j ∈ sigma4PeriodicOneStepNeighborSet L i := by
  classical
  by_cases hij : i = j
  · subst hij
    have hzero : (sigma4PeriodicFullRowStencil L).weight i i = 0 := by
      simpa [sigma4PeriodicFullRowStencil] using
        BoundaryLaplacianFamily.fullRowStencil_weight_self
          sigma4PeriodicBlockStarLaplacianFamily L i
    exact False.elim (hw hzero)
  · have hbox :=
      sigma4PeriodicFullRowStencil_nonzero_weight_cycleOneStepBox L hL hij hw
    simp [sigma4PeriodicOneStepNeighborSet, hbox]

theorem sigma4OpenFullRowStencilActiveTargets_subset_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4OpenFullRowStencilActiveTargets L i ⊆
      sigma4OpenOneStepNeighborSet L i := by
  classical
  intro j hj
  have hw : (sigma4OpenFullRowStencil L).weight i j ≠ 0 := by
    simpa [sigma4OpenFullRowStencilActiveTargets] using hj
  exact sigma4OpenFullRowStencil_nonzero_weight_mem_oneStepNeighborSet L hL hw

theorem sigma4PeriodicFullRowStencilActiveTargets_subset_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    sigma4PeriodicFullRowStencilActiveTargets L i ⊆
      sigma4PeriodicOneStepNeighborSet L i := by
  classical
  intro j hj
  have hw : (sigma4PeriodicFullRowStencil L).weight i j ≠ 0 := by
    simpa [sigma4PeriodicFullRowStencilActiveTargets] using hj
  exact sigma4PeriodicFullRowStencil_nonzero_weight_mem_oneStepNeighborSet L hL hw

theorem sigma4OpenFullRowStencil_weight_eq_zero_of_not_mem_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ sigma4OpenOneStepNeighborSet L i) :
    (sigma4OpenFullRowStencil L).weight i j = 0 := by
  by_contra hw
  exact hnot
    (sigma4OpenFullRowStencil_nonzero_weight_mem_oneStepNeighborSet L hL hw)

theorem sigma4PeriodicFullRowStencil_weight_eq_zero_of_not_mem_oneStepNeighborSet
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ sigma4PeriodicOneStepNeighborSet L i) :
    (sigma4PeriodicFullRowStencil L).weight i j = 0 := by
  by_contra hw
  exact hnot
    (sigma4PeriodicFullRowStencil_nonzero_weight_mem_oneStepNeighborSet L hL hw)

theorem sigma4OpenFullRowStencilActiveTargets_card_le_oneStepNeighborSet_card
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (sigma4OpenFullRowStencilActiveTargets L i).card ≤
      (sigma4OpenOneStepNeighborSet L i).card := by
  exact Finset.card_le_card
    (sigma4OpenFullRowStencilActiveTargets_subset_oneStepNeighborSet L hL i)

theorem sigma4PeriodicFullRowStencilActiveTargets_card_le_oneStepNeighborSet_card
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (sigma4PeriodicFullRowStencilActiveTargets L i).card ≤
      (sigma4PeriodicOneStepNeighborSet L i).card := by
  exact Finset.card_le_card
    (sigma4PeriodicFullRowStencilActiveTargets_subset_oneStepNeighborSet L hL i)

theorem sigma4OpenFullRowStencilActiveTargets_card_le_eighty_one
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (sigma4OpenFullRowStencilActiveTargets L i).card ≤ 81 := by
  exact
    (sigma4OpenFullRowStencilActiveTargets_card_le_oneStepNeighborSet_card
      L hL i).trans
        (sigma4OpenOneStepNeighborSet_card_le_eighty_one L i)

theorem sigma4PeriodicFullRowStencilActiveTargets_card_le_eighty_one
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (sigma4PeriodicFullRowStencilActiveTargets L i).card ≤ 81 := by
  exact
    (sigma4PeriodicFullRowStencilActiveTargets_card_le_oneStepNeighborSet_card
      L hL i).trans
        (sigma4PeriodicOneStepNeighborSet_card_le_eighty_one L i)

/-- Compact reusable row-sparsity certificate for Sigma4 row weights. -/
structure Sigma4RowSparsityCertificate
    (weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ) where
  neighborSet : (L : ℕ) → SigmaCoord4 L → Finset (SigmaCoord4 L)
  activeTargets : (L : ℕ) → SigmaCoord4 L → Finset (SigmaCoord4 L)
  cardBound : ℕ
  activeTargets_mem_iff :
    ∀ L i j, j ∈ activeTargets L i ↔ weight L i j ≠ 0
  nonzero_mem_neighbor :
    ∀ L, 4 ≤ L → ∀ {i j : SigmaCoord4 L},
      weight L i j ≠ 0 → j ∈ neighborSet L i
  zeroOutside :
    ∀ L, 4 ≤ L → ∀ {i j : SigmaCoord4 L},
      j ∉ neighborSet L i → weight L i j = 0
  neighborSet_card_bound :
    ∀ L i, (neighborSet L i).card ≤ cardBound
  activeTargets_card_bound :
    ∀ L, 4 ≤ L → ∀ i, (activeTargets L i).card ≤ cardBound

namespace Sigma4RowSparsityCertificate

theorem activeTargets_subset_neighborSet
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    C.activeTargets L i ⊆ C.neighborSet L i := by
  intro j hj
  exact C.nonzero_mem_neighbor L hL ((C.activeTargets_mem_iff L i j).1 hj)

theorem activeTargets_sum_eq_univ
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (L : ℕ) (i : SigmaCoord4 L) (v : SigmaCoord4 L → ℝ) :
    (C.activeTargets L i).sum (fun j => weight L i j * v j) =
      Finset.univ.sum (fun j => weight L i j * v j) := by
  classical
  refine Finset.sum_subset (fun j _ => Finset.mem_univ j) ?_
  intro j _ hjnot
  have hzero : weight L i j = 0 := by
    by_contra hne
    exact hjnot ((C.activeTargets_mem_iff L i j).2 hne)
  simp [hzero]

noncomputable def localRowAction
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (center : (L : ℕ) → SigmaCoord4 L → ℝ)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) : ℝ :=
  center L i * v i -
    (C.activeTargets L i).sum (fun j => weight L i j * v j)

theorem localRowAction_eq_univRowAction
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (center : (L : ℕ) → SigmaCoord4 L → ℝ)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    C.localRowAction center L v i =
      center L i * v i - Finset.univ.sum (fun j => weight L i j * v j) := by
  simp [localRowAction, C.activeTargets_sum_eq_univ L i v]

noncomputable def localRayleighNumerator
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (center : (L : ℕ) → SigmaCoord4 L → ℝ)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) : ℝ :=
  ∑ i, v i * C.localRowAction center L v i

theorem localRayleighNumerator_eq_mul_normSq_of_localRowAction
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (center : (L : ℕ) → SigmaCoord4 L → ℝ)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (μ : ℝ)
    (hrow : ∀ i, C.localRowAction center L v i = μ * v i) :
    C.localRayleighNumerator center L v = μ * ∑ i, v i * v i := by
  classical
  unfold localRayleighNumerator
  calc
    ∑ i, v i * C.localRowAction center L v i =
        ∑ i, v i * (μ * v i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hrow i]
    _ = ∑ i, μ * (v i * v i) := by
      refine Finset.sum_congr rfl ?_
      intro i _
      ring
    _ = μ * ∑ i, v i * v i := by
      rw [Finset.mul_sum]

theorem localRayleighNumerator_eq_eigenvalue_of_localRowAction
    {weight : (L : ℕ) → SigmaCoord4 L → SigmaCoord4 L → ℝ}
    (C : Sigma4RowSparsityCertificate weight)
    (center : (L : ℕ) → SigmaCoord4 L → ℝ)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (μ : ℝ)
    (hrow : ∀ i, C.localRowAction center L v i = μ * v i)
    (hnorm : (∑ i, v i * v i) = 1) :
    C.localRayleighNumerator center L v = μ := by
  rw [C.localRayleighNumerator_eq_mul_normSq_of_localRowAction
    center L v μ hrow, hnorm, mul_one]

end Sigma4RowSparsityCertificate

noncomputable def sigma4OpenFullRowStencilWeight
    (L : ℕ) (i j : SigmaCoord4 L) : ℝ :=
  (sigma4OpenFullRowStencil L).weight i j

noncomputable def sigma4PeriodicFullRowStencilWeight
    (L : ℕ) (i j : SigmaCoord4 L) : ℝ :=
  (sigma4PeriodicFullRowStencil L).weight i j

noncomputable def sigma4OpenFullRowStencilSparsityCertificate :
    Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight where
  neighborSet := sigma4OpenOneStepNeighborSet
  activeTargets := sigma4OpenFullRowStencilActiveTargets
  cardBound := 81
  activeTargets_mem_iff := by
    intro L i j
    simp [sigma4OpenFullRowStencilActiveTargets,
      sigma4OpenFullRowStencilWeight]
  nonzero_mem_neighbor := by
    intro L hL i j hw
    exact sigma4OpenFullRowStencil_nonzero_weight_mem_oneStepNeighborSet
      L hL hw
  zeroOutside := by
    intro L hL i j hnot
    exact sigma4OpenFullRowStencil_weight_eq_zero_of_not_mem_oneStepNeighborSet
      L hL hnot
  neighborSet_card_bound := by
    intro L i
    exact sigma4OpenOneStepNeighborSet_card_le_eighty_one L i
  activeTargets_card_bound := by
    intro L hL i
    exact sigma4OpenFullRowStencilActiveTargets_card_le_eighty_one L hL i

noncomputable def sigma4PeriodicFullRowStencilSparsityCertificate :
    Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight where
  neighborSet := sigma4PeriodicOneStepNeighborSet
  activeTargets := sigma4PeriodicFullRowStencilActiveTargets
  cardBound := 81
  activeTargets_mem_iff := by
    intro L i j
    simp [sigma4PeriodicFullRowStencilActiveTargets,
      sigma4PeriodicFullRowStencilWeight]
  nonzero_mem_neighbor := by
    intro L hL i j hw
    exact sigma4PeriodicFullRowStencil_nonzero_weight_mem_oneStepNeighborSet
      L hL hw
  zeroOutside := by
    intro L hL i j hnot
    exact sigma4PeriodicFullRowStencil_weight_eq_zero_of_not_mem_oneStepNeighborSet
      L hL hnot
  neighborSet_card_bound := by
    intro L i
    exact sigma4PeriodicOneStepNeighborSet_card_le_eighty_one L i
  activeTargets_card_bound := by
    intro L hL i
    exact sigma4PeriodicFullRowStencilActiveTargets_card_le_eighty_one L hL i

/-- Single package for the open and periodic Sigma4 full-row-stencil sparsity data. -/
structure Sigma4BoundaryFullRowStencilSparsityCertificate where
  openSparsity :
    Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight
  periodicSparsity :
    Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight
  open_cardBound_eq : openSparsity.cardBound = 81
  periodic_cardBound_eq : periodicSparsity.cardBound = 81

noncomputable def sigma4BoundaryFullRowStencilSparsityCertificate :
    Sigma4BoundaryFullRowStencilSparsityCertificate where
  openSparsity := sigma4OpenFullRowStencilSparsityCertificate
  periodicSparsity := sigma4PeriodicFullRowStencilSparsityCertificate
  open_cardBound_eq := rfl
  periodic_cardBound_eq := rfl

noncomputable def sigma4OpenFullRowStencilCenter
    (L : ℕ) (i : SigmaCoord4 L) : ℝ :=
  (sigma4OpenFullRowStencil L).center i

noncomputable def sigma4PeriodicFullRowStencilCenter
    (L : ℕ) (i : SigmaCoord4 L) : ℝ :=
  (sigma4PeriodicFullRowStencil L).center i

theorem sigma4OpenLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    C.localRowAction sigma4OpenFullRowStencilCenter L v i =
      (sigma4OpenFullRowStencil L).rowAction v i := by
  rw [Sigma4RowSparsityCertificate.localRowAction_eq_univRowAction]
  simp only [BoundaryRowStencilAt.rowAction, sigma4OpenFullRowStencilCenter,
    sigma4OpenFullRowStencilWeight, sigma4OpenFullRowStencil,
    BoundaryLaplacianFamily.fullRowStencil]

theorem sigma4PeriodicLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    C.localRowAction sigma4PeriodicFullRowStencilCenter L v i =
      (sigma4PeriodicFullRowStencil L).rowAction v i := by
  rw [Sigma4RowSparsityCertificate.localRowAction_eq_univRowAction]
  simp only [BoundaryRowStencilAt.rowAction, sigma4PeriodicFullRowStencilCenter,
    sigma4PeriodicFullRowStencilWeight, sigma4PeriodicFullRowStencil,
    BoundaryLaplacianFamily.fullRowStencil]

theorem sigma4OpenLocalRowAction_eq_fullRowStencil_rowAction
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    sigma4OpenFullRowStencilSparsityCertificate.localRowAction
        sigma4OpenFullRowStencilCenter L v i =
      (sigma4OpenFullRowStencil L).rowAction v i := by
  exact sigma4OpenLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity
    sigma4OpenFullRowStencilSparsityCertificate L v i

theorem sigma4PeriodicLocalRowAction_eq_fullRowStencil_rowAction
    (L : ℕ) (v : SigmaCoord4 L → ℝ) (i : SigmaCoord4 L) :
    sigma4PeriodicFullRowStencilSparsityCertificate.localRowAction
        sigma4PeriodicFullRowStencilCenter L v i =
      (sigma4PeriodicFullRowStencil L).rowAction v i := by
  exact sigma4PeriodicLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity
    sigma4PeriodicFullRowStencilSparsityCertificate L v i

theorem sigma4OpenLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    C.localRayleighNumerator sigma4OpenFullRowStencilCenter L v =
      (sigma4OpenFullRowStencil L).rayleighNumerator v := by
  classical
  unfold Sigma4RowSparsityCertificate.localRayleighNumerator
  unfold BoundaryRowStencilAt.rayleighNumerator
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sigma4OpenLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity C]

theorem sigma4PeriodicLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    C.localRayleighNumerator sigma4PeriodicFullRowStencilCenter L v =
      (sigma4PeriodicFullRowStencil L).rayleighNumerator v := by
  classical
  unfold Sigma4RowSparsityCertificate.localRayleighNumerator
  unfold BoundaryRowStencilAt.rayleighNumerator
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [sigma4PeriodicLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity C]

theorem sigma4OpenLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    sigma4OpenFullRowStencilSparsityCertificate.localRayleighNumerator
        sigma4OpenFullRowStencilCenter L v =
      (sigma4OpenFullRowStencil L).rayleighNumerator v := by
  exact
    sigma4OpenLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
      sigma4OpenFullRowStencilSparsityCertificate L v

theorem sigma4PeriodicLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    sigma4PeriodicFullRowStencilSparsityCertificate.localRayleighNumerator
        sigma4PeriodicFullRowStencilCenter L v =
      (sigma4PeriodicFullRowStencil L).rayleighNumerator v := by
  exact
    sigma4PeriodicLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
      sigma4PeriodicFullRowStencilSparsityCertificate L v

theorem sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    C.localRayleighNumerator sigma4OpenFullRowStencilCenter L v =
      sigma4BlockStarOpenLaplacianFamily.nodeDot L v
        (sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L v) := by
  rw [
    sigma4OpenLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
      C]
  exact (sigma4OpenFullRowStencil L).rayleighNumerator_eq_nodeDot_laplacianMulVec v

theorem sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    (C : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    C.localRayleighNumerator sigma4PeriodicFullRowStencilCenter L v =
      sigma4PeriodicBlockStarLaplacianFamily.nodeDot L v
        (sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v) := by
  rw [
    sigma4PeriodicLocalRayleighNumerator_eq_fullRowStencil_rayleighNumerator_of_sparsity
      C]
  exact (sigma4PeriodicFullRowStencil L).rayleighNumerator_eq_nodeDot_laplacianMulVec v

theorem sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    sigma4OpenFullRowStencilSparsityCertificate.localRayleighNumerator
        sigma4OpenFullRowStencilCenter L v =
      sigma4BlockStarOpenLaplacianFamily.nodeDot L v
        (sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L v) := by
  exact sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    sigma4OpenFullRowStencilSparsityCertificate L v

theorem sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    sigma4PeriodicFullRowStencilSparsityCertificate.localRayleighNumerator
        sigma4PeriodicFullRowStencilCenter L v =
      sigma4PeriodicBlockStarLaplacianFamily.nodeDot L v
        (sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v) := by
  exact sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    sigma4PeriodicFullRowStencilSparsityCertificate L v

/--
Open-boundary Sigma4 upper witness stated in local sparse Rayleigh form.
The local Rayleigh numerator is the one computed only over active row targets.
-/
structure Sigma4OpenLocalRayleighUpperWitnessCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, SigmaCoord4 L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_norm_one :
    ∀ L, L0 ≤ L →
      sigma4BlockStarOpenLaplacianFamily.nodeNormSq L (eigenmode L) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L →
      sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L (eigenmode L) =
        fun i => eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  localRayleigh_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * sparsity.localRayleighNumerator
        sigma4OpenFullRowStencilCenter L (eigenmode L) ≤ coefficient + upperError L

namespace Sigma4OpenLocalRayleighUpperWitnessCertificateAt

noncomputable def toBoundaryRayleighUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRayleighUpperWitnessCertificateAt coefficient L0) :
    BoundaryRayleighUpperWitnessCertificateAt
      sigma4BlockStarOpenLaplacianFamily coefficient L0 where
  L0_pos := C.L0_pos
  upperError := C.upperError
  upperError_tendsto_zero := C.upperError_tendsto_zero
  eigenvalue := C.eigenvalue
  eigenmode := C.eigenmode
  eigenmode_ne_zero := C.eigenmode_ne_zero
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  eigenvalue_ne_zero := C.eigenvalue_ne_zero
  rayleigh_upper := by
    intro L hL
    rw [← sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
      C.sparsity L (C.eigenmode L)]
    exact C.localRayleigh_upper L hL

noncomputable def toEigenmodeUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRayleighUpperWitnessCertificateAt coefficient L0) :
    BoundaryEigenmodeUpperWitnessCertificateAt
      sigma4BlockStarOpenLaplacianFamily coefficient L0 :=
  C.toBoundaryRayleighUpperWitness.toEigenmodeUpperWitness

end Sigma4OpenLocalRayleighUpperWitnessCertificateAt

/-- Periodic Sigma4 upper witness stated in local sparse Rayleigh form. -/
structure Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, SigmaCoord4 L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_norm_one :
    ∀ L, L0 ≤ L →
      sigma4PeriodicBlockStarLaplacianFamily.nodeNormSq L (eigenmode L) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L →
      sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L (eigenmode L) =
        fun i => eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  localRayleigh_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * sparsity.localRayleighNumerator
        sigma4PeriodicFullRowStencilCenter L (eigenmode L) ≤ coefficient + upperError L

namespace Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt

noncomputable def toBoundaryRayleighUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt coefficient L0) :
    BoundaryRayleighUpperWitnessCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily coefficient L0 where
  L0_pos := C.L0_pos
  upperError := C.upperError
  upperError_tendsto_zero := C.upperError_tendsto_zero
  eigenvalue := C.eigenvalue
  eigenmode := C.eigenmode
  eigenmode_ne_zero := C.eigenmode_ne_zero
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  eigenvalue_ne_zero := C.eigenvalue_ne_zero
  rayleigh_upper := by
    intro L hL
    rw [← sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
      C.sparsity L (C.eigenmode L)]
    exact C.localRayleigh_upper L hL

noncomputable def toEigenmodeUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt coefficient L0) :
    BoundaryEigenmodeUpperWitnessCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily coefficient L0 :=
  C.toBoundaryRayleighUpperWitness.toEigenmodeUpperWitness

end Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt

/--
Open-boundary Sigma4 upper witness reduced to the local row-action identity
`localRowAction = μ v`.  This is the finite-stencil obligation needed before
the Rayleigh upper witness is automatic.
-/
structure Sigma4OpenLocalRowActionUpperWitnessCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, SigmaCoord4 L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_norm_one :
    ∀ L, L0 ≤ L →
      sigma4BlockStarOpenLaplacianFamily.nodeNormSq L (eigenmode L) = 1
  localRowAction_eq :
    ∀ L, L0 ≤ L → ∀ i,
      sparsity.localRowAction sigma4OpenFullRowStencilCenter L (eigenmode L) i =
        eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  eigenvalue_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * eigenvalue L ≤ coefficient + upperError L

namespace Sigma4OpenLocalRowActionUpperWitnessCertificateAt

theorem eigenmode_eq
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    ∀ L, L0 ≤ L →
      sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L (C.eigenmode L) =
        fun i => C.eigenvalue L * C.eigenmode L i := by
  intro L hL
  ext i
  calc
    sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L (C.eigenmode L) i =
        (sigma4OpenFullRowStencil L).rowAction (C.eigenmode L) i := by
      rw [(sigma4OpenFullRowStencil L).rowAction_eq_laplacianMulVec]
    _ = C.sparsity.localRowAction
          sigma4OpenFullRowStencilCenter L (C.eigenmode L) i := by
      rw [sigma4OpenLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity]
    _ = C.eigenvalue L * C.eigenmode L i :=
      C.localRowAction_eq L hL i

noncomputable def toLocalRayleighUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    Sigma4OpenLocalRayleighUpperWitnessCertificateAt coefficient L0 where
  sparsity := C.sparsity
  L0_pos := C.L0_pos
  upperError := C.upperError
  upperError_tendsto_zero := C.upperError_tendsto_zero
  eigenvalue := C.eigenvalue
  eigenmode := C.eigenmode
  eigenmode_ne_zero := C.eigenmode_ne_zero
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  eigenvalue_ne_zero := C.eigenvalue_ne_zero
  localRayleigh_upper := by
    intro L hL
    have hnorm : (∑ i, C.eigenmode L i * C.eigenmode L i) = 1 := by
      simpa [BoundaryLaplacianFamily.nodeNormSq,
        BoundaryLaplacianFamily.nodeDot, dotProduct] using
        C.eigenmode_norm_one L hL
    have hray :=
      C.sparsity.localRayleighNumerator_eq_eigenvalue_of_localRowAction
        sigma4OpenFullRowStencilCenter L (C.eigenmode L) (C.eigenvalue L)
        (C.localRowAction_eq L hL) hnorm
    rw [hray]
    exact C.eigenvalue_upper L hL

noncomputable def toEigenmodeUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    BoundaryEigenmodeUpperWitnessCertificateAt
      sigma4BlockStarOpenLaplacianFamily coefficient L0 :=
  C.toLocalRayleighUpperWitness.toEigenmodeUpperWitness

end Sigma4OpenLocalRowActionUpperWitnessCertificateAt

/-- Periodic Sigma4 upper witness reduced to the local row-action identity. -/
structure Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight
  L0_pos : 0 < L0
  upperError : ℕ → ℝ
  upperError_tendsto_zero :
    Filter.Tendsto upperError Filter.atTop (nhds 0)
  eigenvalue : ℕ → ℝ
  eigenmode : ∀ L, SigmaCoord4 L → ℝ
  eigenmode_ne_zero : ∀ L, L0 ≤ L → eigenmode L ≠ 0
  eigenmode_norm_one :
    ∀ L, L0 ≤ L →
      sigma4PeriodicBlockStarLaplacianFamily.nodeNormSq L (eigenmode L) = 1
  localRowAction_eq :
    ∀ L, L0 ≤ L → ∀ i,
      sparsity.localRowAction sigma4PeriodicFullRowStencilCenter L (eigenmode L) i =
        eigenvalue L * eigenmode L i
  eigenvalue_ne_zero : ∀ L, L0 ≤ L → eigenvalue L ≠ 0
  eigenvalue_upper :
    ∀ L, L0 ≤ L →
      (L : ℝ) ^ 2 * eigenvalue L ≤ coefficient + upperError L

namespace Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt

theorem eigenmode_eq
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    ∀ L, L0 ≤ L →
      sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L (C.eigenmode L) =
        fun i => C.eigenvalue L * C.eigenmode L i := by
  intro L hL
  ext i
  calc
    sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L (C.eigenmode L) i =
        (sigma4PeriodicFullRowStencil L).rowAction (C.eigenmode L) i := by
      rw [(sigma4PeriodicFullRowStencil L).rowAction_eq_laplacianMulVec]
    _ = C.sparsity.localRowAction
          sigma4PeriodicFullRowStencilCenter L (C.eigenmode L) i := by
      rw [sigma4PeriodicLocalRowAction_eq_fullRowStencil_rowAction_of_sparsity]
    _ = C.eigenvalue L * C.eigenmode L i :=
      C.localRowAction_eq L hL i

noncomputable def toLocalRayleighUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt coefficient L0 where
  sparsity := C.sparsity
  L0_pos := C.L0_pos
  upperError := C.upperError
  upperError_tendsto_zero := C.upperError_tendsto_zero
  eigenvalue := C.eigenvalue
  eigenmode := C.eigenmode
  eigenmode_ne_zero := C.eigenmode_ne_zero
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  eigenvalue_ne_zero := C.eigenvalue_ne_zero
  localRayleigh_upper := by
    intro L hL
    have hnorm : (∑ i, C.eigenmode L i * C.eigenmode L i) = 1 := by
      simpa [BoundaryLaplacianFamily.nodeNormSq,
        BoundaryLaplacianFamily.nodeDot, dotProduct] using
        C.eigenmode_norm_one L hL
    have hray :=
      C.sparsity.localRayleighNumerator_eq_eigenvalue_of_localRowAction
        sigma4PeriodicFullRowStencilCenter L (C.eigenmode L) (C.eigenvalue L)
        (C.localRowAction_eq L hL) hnorm
    rw [hray]
    exact C.eigenvalue_upper L hL

noncomputable def toEigenmodeUpperWitness
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt coefficient L0) :
    BoundaryEigenmodeUpperWitnessCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily coefficient L0 :=
  C.toLocalRayleighUpperWitness.toEigenmodeUpperWitness

end Sigma4PeriodicLocalRowActionUpperWitnessCertificateAt

/--
Open-boundary Sigma4 lower certificate in local sparse Rayleigh form.  It is
parameterised by a normalized eigenmode for each non-zero spectral value.
-/
structure Sigma4OpenLocalRayleighSpectralLowerCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4OpenFullRowStencilWeight
  L0_pos : 0 < L0
  lowerError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  eigenmode : ∀ L, ℝ → SigmaCoord4 L → ℝ
  eigenmode_norm_one :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        sigma4BlockStarOpenLaplacianFamily.nodeNormSq L (eigenmode L μ) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L (eigenmode L μ) =
          fun i => μ * eigenmode L μ i
  localRayleigh_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        coefficient - lowerError L ≤
          (L : ℝ) ^ 2 * sparsity.localRayleighNumerator
            sigma4OpenFullRowStencilCenter L (eigenmode L μ)

namespace Sigma4OpenLocalRayleighSpectralLowerCertificateAt

noncomputable def toBoundaryRayleighSpectralLower
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRayleighSpectralLowerCertificateAt coefficient L0) :
    BoundaryRayleighSpectralLowerCertificateAt
      sigma4BlockStarOpenLaplacianFamily coefficient L0 where
  L0_pos := C.L0_pos
  lowerError := C.lowerError
  lowerError_tendsto_zero := C.lowerError_tendsto_zero
  eigenmode := C.eigenmode
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  rayleigh_lower := by
    intro L hL μ hμmem hμne
    rw [← sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
      C.sparsity L (C.eigenmode L μ)]
    exact C.localRayleigh_lower L hL μ hμmem hμne

noncomputable def toRescaledSpectralLower
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRayleighSpectralLowerCertificateAt coefficient L0) :
    BoundaryRescaledSpectralLowerCertificateAt
      sigma4BlockStarOpenLaplacianFamily coefficient L0 :=
  C.toBoundaryRayleighSpectralLower.toRescaledSpectralLower

end Sigma4OpenLocalRayleighSpectralLowerCertificateAt

/-- Periodic Sigma4 lower certificate in local sparse Rayleigh form. -/
structure Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt
    (coefficient : ℝ) (L0 : ℕ) where
  sparsity : Sigma4RowSparsityCertificate sigma4PeriodicFullRowStencilWeight
  L0_pos : 0 < L0
  lowerError : ℕ → ℝ
  lowerError_tendsto_zero :
    Filter.Tendsto lowerError Filter.atTop (nhds 0)
  eigenmode : ∀ L, ℝ → SigmaCoord4 L → ℝ
  eigenmode_norm_one :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        sigma4PeriodicBlockStarLaplacianFamily.nodeNormSq L (eigenmode L μ) = 1
  eigenmode_eq :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L (eigenmode L μ) =
          fun i => μ * eigenmode L μ i
  localRayleigh_lower :
    ∀ L, L0 ≤ L → ∀ μ ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L,
      μ ≠ 0 →
        coefficient - lowerError L ≤
          (L : ℝ) ^ 2 * sparsity.localRayleighNumerator
            sigma4PeriodicFullRowStencilCenter L (eigenmode L μ)

namespace Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt

noncomputable def toBoundaryRayleighSpectralLower
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt coefficient L0) :
    BoundaryRayleighSpectralLowerCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily coefficient L0 where
  L0_pos := C.L0_pos
  lowerError := C.lowerError
  lowerError_tendsto_zero := C.lowerError_tendsto_zero
  eigenmode := C.eigenmode
  eigenmode_norm_one := C.eigenmode_norm_one
  eigenmode_eq := C.eigenmode_eq
  rayleigh_lower := by
    intro L hL μ hμmem hμne
    rw [← sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
      C.sparsity L (C.eigenmode L μ)]
    exact C.localRayleigh_lower L hL μ hμmem hμne

noncomputable def toRescaledSpectralLower
    {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt coefficient L0) :
    BoundaryRescaledSpectralLowerCertificateAt
      sigma4PeriodicBlockStarLaplacianFamily coefficient L0 :=
  C.toBoundaryRayleighSpectralLower.toRescaledSpectralLower

end Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt

/-- Open-boundary Sigma4 split certificate assembled from local Rayleigh lower and upper data. -/
structure Sigma4OpenLocalRayleighSplitCertificateAt
    (lambda : ℕ → ℝ) (coefficient : ℝ) (L0 : ℕ) where
  realization : BoundarySpectralValueRealizationFrom
    sigma4BlockStarOpenLaplacianFamily lambda L0
  lower : Sigma4OpenLocalRayleighSpectralLowerCertificateAt coefficient L0
  upper : Sigma4OpenLocalRayleighUpperWitnessCertificateAt coefficient L0

namespace Sigma4OpenLocalRayleighSplitCertificateAt

noncomputable def toBoundarySplitEigenmode
    {lambda : ℕ → ℝ} {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4OpenLocalRayleighSplitCertificateAt lambda coefficient L0) :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4BlockStarOpenLaplacianFamily lambda coefficient where
  L0 := L0
  realization := C.realization
  lower := C.lower.toRescaledSpectralLower
  upper := C.upper.toEigenmodeUpperWitness

end Sigma4OpenLocalRayleighSplitCertificateAt

/-- Periodic Sigma4 split certificate assembled from local Rayleigh lower and upper data. -/
structure Sigma4PeriodicLocalRayleighSplitCertificateAt
    (lambda : ℕ → ℝ) (coefficient : ℝ) (L0 : ℕ) where
  realization : BoundarySpectralValueRealizationFrom
    sigma4PeriodicBlockStarLaplacianFamily lambda L0
  lower : Sigma4PeriodicLocalRayleighSpectralLowerCertificateAt coefficient L0
  upper : Sigma4PeriodicLocalRayleighUpperWitnessCertificateAt coefficient L0

namespace Sigma4PeriodicLocalRayleighSplitCertificateAt

noncomputable def toBoundarySplitEigenmode
    {lambda : ℕ → ℝ} {coefficient : ℝ} {L0 : ℕ}
    (C : Sigma4PeriodicLocalRayleighSplitCertificateAt lambda coefficient L0) :
    BoundarySplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily lambda coefficient where
  L0 := L0
  realization := C.realization
  lower := C.lower.toRescaledSpectralLower
  upper := C.upper.toEigenmodeUpperWitness

end Sigma4PeriodicLocalRayleighSplitCertificateAt

/--
Open/periodic Sigma4 continuum split package in local sparse Rayleigh form.
This is the local-stencil version of the existing split eigenmode bracketing
interface.
-/
structure Sigma4BoundaryLocalRayleighContinuumSplitCertificate
    (periodicLambda openLambda : ℕ → ℝ) where
  D_eff : ℝ
  D_eff_pos : 0 < D_eff
  periodicL0 : ℕ
  openL0 : ℕ
  periodic :
    Sigma4PeriodicLocalRayleighSplitCertificateAt periodicLambda
      (periodicSpectralContinuumCoefficient D_eff) periodicL0
  openBoundary :
    Sigma4OpenLocalRayleighSplitCertificateAt openLambda
      (openSpectralContinuumCoefficient D_eff) openL0

namespace Sigma4BoundaryLocalRayleighContinuumSplitCertificate

noncomputable def toBoundaryContinuumSplitEigenmode
    {periodicLambda openLambda : ℕ → ℝ}
    (C : Sigma4BoundaryLocalRayleighContinuumSplitCertificate
      periodicLambda openLambda) :
    BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      periodicLambda openLambda where
  D_eff := C.D_eff
  D_eff_pos := C.D_eff_pos
  periodic := C.periodic.toBoundarySplitEigenmode
  openBoundary := C.openBoundary.toBoundarySplitEigenmode

end Sigma4BoundaryLocalRayleighContinuumSplitCertificate

/-- Concrete open/periodic Sigma boundary spectral programme. -/
structure Sigma4ConcreteBoundarySpectralLimitProgram where
  periodicLambda : ℕ → ℝ
  openLambda : ℕ → ℝ
  periodicRealization :
    BoundarySpectralValueRealization sigma4PeriodicBlockStarLaplacianFamily periodicLambda
  openRealization :
    BoundarySpectralValueRealization sigma4BlockStarOpenLaplacianFamily openLambda
  limit : BoundaryContinuumLimitCertificate periodicLambda openLambda

namespace Sigma4ConcreteBoundarySpectralLimitProgram

noncomputable def toSigma4BoundarySpectralLimitProgram
    (P : Sigma4ConcreteBoundarySpectralLimitProgram) : Sigma4BoundarySpectralLimitProgram where
  periodic := sigma4PeriodicBlockStarSpectrallyClosedFamily
  periodicLambda := P.periodicLambda
  openLambda := P.openLambda
  periodicRealization := P.periodicRealization
  openRealization := P.openRealization
  limit := P.limit

noncomputable def periodicScaling (P : Sigma4ConcreteBoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.periodicLambda :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling (P : Sigma4ConcreteBoundarySpectralLimitProgram) :
    InverseSquareSpectralScaling P.openLambda :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK (P : Sigma4ConcreteBoundarySpectralLimitProgram) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0 (P : Sigma4ConcreteBoundarySpectralLimitProgram) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4ConcreteBoundarySpectralLimitProgram) :
    BoundaryDifferenceInverseSquareBound P.periodicLambda P.openLambda
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

end Sigma4ConcreteBoundarySpectralLimitProgram

/--
Concrete boundary spectral programme enriched with the closed finite-row
sparsity certificate for the open and periodic Sigma4 full row stencils.
-/
structure Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity where
  spectral : Sigma4ConcreteBoundarySpectralLimitProgram
  sparsity : Sigma4BoundaryFullRowStencilSparsityCertificate

namespace Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgram
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity) :
    Sigma4ConcreteBoundarySpectralLimitProgram :=
  P.spectral

noncomputable def toSigma4BoundarySpectralLimitProgram
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity) :
    Sigma4BoundarySpectralLimitProgram :=
  P.spectral.toSigma4BoundarySpectralLimitProgram

theorem open_zeroOutside
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.sparsity.openSparsity.neighborSet L i) :
    (sigma4OpenFullRowStencil L).weight i j = 0 := by
  simpa [sigma4OpenFullRowStencilWeight] using
    P.sparsity.openSparsity.zeroOutside L hL hnot

theorem periodic_zeroOutside
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.sparsity.periodicSparsity.neighborSet L i) :
    (sigma4PeriodicFullRowStencil L).weight i j = 0 := by
  simpa [sigma4PeriodicFullRowStencilWeight] using
    P.sparsity.periodicSparsity.zeroOutside L hL hnot

theorem open_activeTargets_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.sparsity.openSparsity.activeTargets L i).card ≤ 81 := by
  have h := P.sparsity.openSparsity.activeTargets_card_bound L hL i
  simpa [P.sparsity.open_cardBound_eq] using h

theorem periodic_activeTargets_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.sparsity.periodicSparsity.activeTargets L i).card ≤ 81 := by
  have h := P.sparsity.periodicSparsity.activeTargets_card_bound L hL i
  simpa [P.sparsity.periodic_cardBound_eq] using h

theorem open_neighborSet_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (i : SigmaCoord4 L) :
    (P.sparsity.openSparsity.neighborSet L i).card ≤ 81 := by
  have h := P.sparsity.openSparsity.neighborSet_card_bound L i
  simpa [P.sparsity.open_cardBound_eq] using h

theorem periodic_neighborSet_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity)
    (L : ℕ) (i : SigmaCoord4 L) :
    (P.sparsity.periodicSparsity.neighborSet L i).card ≤ 81 := by
  have h := P.sparsity.periodicSparsity.neighborSet_card_bound L i
  simpa [P.sparsity.periodic_cardBound_eq] using h

end Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity

namespace Sigma4ConcreteBoundarySpectralLimitProgram

noncomputable def withSparsity
    (P : Sigma4ConcreteBoundarySpectralLimitProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramWithSparsity where
  spectral := P
  sparsity := sigma4BoundaryFullRowStencilSparsityCertificate

end Sigma4ConcreteBoundarySpectralLimitProgram

/--
Concrete open/periodic Sigma boundary spectral programme with eventual
first-positive eigenvalue realizations.
-/
structure Sigma4ConcreteBoundarySpectralLimitProgramFrom where
  periodicLambda : ℕ → ℝ
  openLambda : ℕ → ℝ
  periodicL0 : ℕ
  openL0 : ℕ
  periodicRealization :
    BoundarySpectralValueRealizationFrom
      sigma4PeriodicBlockStarLaplacianFamily periodicLambda periodicL0
  openRealization :
    BoundarySpectralValueRealizationFrom
      sigma4BlockStarOpenLaplacianFamily openLambda openL0
  limit : BoundaryContinuumLimitCertificate periodicLambda openLambda

namespace Sigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def toBoundarySpectralLimitProgramFrom
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) :
    BoundarySpectralLimitProgramFrom where
  periodicFamily := sigma4PeriodicBlockStarLaplacianFamily
  openFamily := sigma4BlockStarOpenLaplacianFamily
  periodicLambda := P.periodicLambda
  openLambda := P.openLambda
  periodicL0 := P.periodicL0
  openL0 := P.openL0
  periodicRealization := P.periodicRealization
  openRealization := P.openRealization
  limit := P.limit

noncomputable def periodicScaling
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) :
    InverseSquareSpectralScaling P.periodicLambda :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) :
    InverseSquareSpectralScaling P.openLambda :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) :
    BoundaryDifferenceInverseSquareBound P.periodicLambda P.openLambda
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

theorem periodic_value_mem
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom)
    {L : ℕ} (hL : P.periodicL0 ≤ L) :
    P.periodicLambda L ∈ sigma4PeriodicBlockStarLaplacianFamily.spectralSet L :=
  P.periodicRealization.value_mem L hL

theorem open_value_mem
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom)
    {L : ℕ} (hL : P.openL0 ≤ L) :
    P.openLambda L ∈ sigma4BlockStarOpenLaplacianFamily.spectralSet L :=
  P.openRealization.value_mem L hL

end Sigma4ConcreteBoundarySpectralLimitProgramFrom

/--
Eventual-realization boundary spectral programme enriched with the same concrete
open/periodic full-row-stencil sparsity data.
-/
structure Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity where
  spectral : Sigma4ConcreteBoundarySpectralLimitProgramFrom
  sparsity : Sigma4BoundaryFullRowStencilSparsityCertificate

namespace Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.spectral

noncomputable def toBoundarySpectralLimitProgramFrom
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity) :
    BoundarySpectralLimitProgramFrom :=
  P.spectral.toBoundarySpectralLimitProgramFrom

theorem open_zeroOutside
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.sparsity.openSparsity.neighborSet L i) :
    (sigma4OpenFullRowStencil L).weight i j = 0 := by
  simpa [sigma4OpenFullRowStencilWeight] using
    P.sparsity.openSparsity.zeroOutside L hL hnot

theorem periodic_zeroOutside
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.sparsity.periodicSparsity.neighborSet L i) :
    (sigma4PeriodicFullRowStencil L).weight i j = 0 := by
  simpa [sigma4PeriodicFullRowStencilWeight] using
    P.sparsity.periodicSparsity.zeroOutside L hL hnot

theorem open_activeTargets_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.sparsity.openSparsity.activeTargets L i).card ≤ 81 := by
  have h := P.sparsity.openSparsity.activeTargets_card_bound L hL i
  simpa [P.sparsity.open_cardBound_eq] using h

theorem periodic_activeTargets_card_le_eighty_one
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.sparsity.periodicSparsity.activeTargets L i).card ≤ 81 := by
  have h := P.sparsity.periodicSparsity.activeTargets_card_bound L hL i
  simpa [P.sparsity.periodic_cardBound_eq] using h

end Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity

namespace Sigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def withSparsity
    (P : Sigma4ConcreteBoundarySpectralLimitProgramFrom) :
    Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity where
  spectral := P
  sparsity := sigma4BoundaryFullRowStencilSparsityCertificate

end Sigma4ConcreteBoundarySpectralLimitProgramFrom

/--
Concrete Sigma boundary programme after the finite spectral selection has been
closed.  The only remaining input is the continuum limit for the selected first
positive open and periodic eigenvalue sequences.
-/
structure Sigma4FirstPositiveBoundaryContinuumLimitProgram where
  limit :
    BoundaryContinuumLimitCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom where
  periodicLambda := sigma4PeriodicFirstPositiveSpectralValue
  openLambda := sigma4OpenFirstPositiveSpectralValue
  periodicL0 := 4
  openL0 := 4
  periodicRealization := sigma4PeriodicFirstPositiveSpectralValueRealization
  openRealization := sigma4OpenFirstPositiveSpectralValueRealization
  limit := P.limit

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  BoundaryContinuumLimitCertificate.periodicScaling P.limit

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  BoundaryContinuumLimitCertificate.openScaling P.limit

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) : ℝ :=
  BoundaryContinuumLimitCertificate.differenceK P.limit

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) : ℕ :=
  BoundaryContinuumLimitCertificate.differenceL0 P.limit

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact BoundaryContinuumLimitCertificate.boundaryDifferenceInverseSquareBound P.limit

theorem periodic_value_mem
    {L : ℕ} (hL : 4 ≤ L) :
    sigma4PeriodicFirstPositiveSpectralValue L ∈
      sigma4PeriodicBlockStarLaplacianFamily.spectralSet L :=
  sigma4PeriodicFirstPositiveSpectralValueRealization.value_mem L hL

theorem open_value_mem
    {L : ℕ} (hL : 4 ≤ L) :
    sigma4OpenFirstPositiveSpectralValue L ∈
      sigma4BlockStarOpenLaplacianFamily.spectralSet L :=
  sigma4OpenFirstPositiveSpectralValueRealization.value_mem L hL

end Sigma4FirstPositiveBoundaryContinuumLimitProgram

/--
Concrete first-positive boundary programme in homogenization-error form.  This
is equivalent to the continuum-limit programme, but exposes the analytic rest
as convergence of the two rescaled errors to zero.
-/
structure Sigma4FirstPositiveBoundaryErrorProgram where
  error :
    BoundaryContinuumErrorCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram where
  limit := P.error.toLimit

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryErrorProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryErrorProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryErrorProgram

/--
Concrete first-positive boundary programme in absolute-error-bound form.  This
is the estimate-level input expected from a source-grounded homogenization
argument.
-/
structure Sigma4FirstPositiveBoundaryAbsErrorBoundProgram where
  absError :
    BoundaryContinuumAbsErrorBoundCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryAbsErrorBoundProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram where
  error := P.absError.toError

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toErrorProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryAbsErrorBoundProgram

/--
Concrete first-positive boundary programme with inverse-linear rescaled
eigenvalue errors.
-/
structure Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram where
  inverseLinearError :
    BoundaryContinuumInverseLinearErrorBoundCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram where
  absError := P.inverseLinearError.toAbsError

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toAbsErrorProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toAbsErrorProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram

/--
Concrete first-positive boundary programme with cubic eigenvalue-level
finite-size errors.
-/
structure Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram where
  cubicEigenvalueError :
    BoundaryContinuumCubicEigenvalueErrorBoundCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram

noncomputable def toInverseLinearErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram where
  inverseLinearError := P.cubicEigenvalueError.toInverseLinear

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram :=
  P.toInverseLinearErrorProgram.toAbsErrorProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toInverseLinearErrorProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toInverseLinearErrorProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram

/--
Concrete first-positive boundary programme in spectral-bracketing form.  This
is the remaining source-facing task: prove a lower bracket for all positive
spectral values and an upper witness for the open and periodic families.
-/
structure Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram where
  bracketing :
    BoundaryContinuumCubicSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram

noncomputable def toCubicEigenvalueErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram where
  cubicEigenvalueError := P.bracketing.toCubicEigenvalueError

noncomputable def toInverseLinearErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram :=
  P.toCubicEigenvalueErrorProgram.toInverseLinearErrorProgram

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram :=
  P.toCubicEigenvalueErrorProgram.toAbsErrorProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toCubicEigenvalueErrorProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toCubicEigenvalueErrorProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram

/--
Concrete first-positive boundary programme in rescaled spectral-bracketing
form.  This is the source-level homogenisation interface matching
`L^ 2 λ(L) → C`.
-/
structure Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram where
  bracketing :
    BoundaryContinuumRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram where
  absError := P.bracketing.toAbsError

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toAbsErrorProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toAbsErrorProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) : ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) : ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram

/--
Concrete first-positive boundary programme with explicit positive spectral
witnesses for the rescaled upper brackets.
-/
structure Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram where
  bracketing :
    BoundaryContinuumExplicitRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram

noncomputable def toRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram where
  bracketing := P.bracketing.toRescaledSpectralBracketing

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram :=
  P.toRescaledSpectralBracketingProgram.toAbsErrorProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toRescaledSpectralBracketingProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toRescaledSpectralBracketingProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram

/--
Concrete first-positive boundary programme with eigenmode witnesses for the
rescaled upper brackets.
-/
structure Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram where
  bracketing :
    BoundaryContinuumEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram

noncomputable def toExplicitRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram where
  bracketing := P.bracketing.toExplicitRescaledSpectralBracketing

noncomputable def toRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram :=
  P.toExplicitRescaledSpectralBracketingProgram.toRescaledSpectralBracketingProgram

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram :=
  P.toRescaledSpectralBracketingProgram.toAbsErrorProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toRescaledSpectralBracketingProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toRescaledSpectralBracketingProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram

/--
Concrete first-positive boundary programme whose remaining analytic input is
split into lower spectral coercivity and explicit eigenmode upper witnesses.
-/
structure Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram where
  bracketing :
    BoundaryContinuumSplitEigenmodeRescaledSpectralBracketingCertificate
      sigma4PeriodicBlockStarLaplacianFamily
      sigma4BlockStarOpenLaplacianFamily
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram

noncomputable def toEigenmodeRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram where
  bracketing := P.bracketing.toEigenmodeRescaledSpectralBracketing

noncomputable def toExplicitRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram :=
  P.toEigenmodeRescaledSpectralBracketingProgram
    |>.toExplicitRescaledSpectralBracketingProgram

noncomputable def toRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram :=
  P.toEigenmodeRescaledSpectralBracketingProgram
    |>.toRescaledSpectralBracketingProgram

noncomputable def toAbsErrorProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryAbsErrorBoundProgram :=
  P.toRescaledSpectralBracketingProgram.toAbsErrorProgram

noncomputable def toErrorProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryErrorProgram :=
  P.toRescaledSpectralBracketingProgram.toErrorProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toRescaledSpectralBracketingProgram.toContinuumLimitProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.toContinuumLimitProgram.toSigma4ConcreteBoundarySpectralLimitProgramFrom

noncomputable def periodicScaling
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4PeriodicFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.periodicScaling

noncomputable def openScaling
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    InverseSquareSpectralScaling sigma4OpenFirstPositiveSpectralValue :=
  P.toContinuumLimitProgram.openScaling

noncomputable def differenceK
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    ℝ :=
  P.toContinuumLimitProgram.differenceK

noncomputable def differenceL0
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    ℕ :=
  P.toContinuumLimitProgram.differenceL0

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.differenceK P.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram

/--
First-positive boundary spectral programme together with the concrete finite
row-sparsity data of the open and periodic Sigma4 block-star operators.
-/
structure Sigma4FirstPositiveBoundaryLocalSpectralProgram where
  concrete : Sigma4ConcreteBoundarySpectralLimitProgramFromWithSparsity
  periodicLambda_eq :
    concrete.spectral.periodicLambda = sigma4PeriodicFirstPositiveSpectralValue
  openLambda_eq :
    concrete.spectral.openLambda = sigma4OpenFirstPositiveSpectralValue
  periodicL0_eq : concrete.spectral.periodicL0 = 4
  openL0_eq : concrete.spectral.openL0 = 4

namespace Sigma4FirstPositiveBoundaryLocalSpectralProgram

noncomputable def toSigma4ConcreteBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram) :
    Sigma4ConcreteBoundarySpectralLimitProgramFrom :=
  P.concrete.spectral

noncomputable def toBoundarySpectralLimitProgramFrom
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram) :
    BoundarySpectralLimitProgramFrom :=
  P.concrete.toBoundarySpectralLimitProgramFrom

theorem periodicLambda_apply
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram) (L : ℕ) :
    P.concrete.spectral.periodicLambda L =
      sigma4PeriodicFirstPositiveSpectralValue L := by
  rw [P.periodicLambda_eq]

theorem openLambda_apply
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram) (L : ℕ) :
    P.concrete.spectral.openLambda L =
      sigma4OpenFirstPositiveSpectralValue L := by
  rw [P.openLambda_eq]

theorem open_zeroOutside
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.concrete.sparsity.openSparsity.neighborSet L i) :
    (sigma4OpenFullRowStencil L).weight i j = 0 :=
  P.concrete.open_zeroOutside L hL hnot

theorem periodic_zeroOutside
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (hL : 4 ≤ L) {i j : SigmaCoord4 L}
    (hnot : j ∉ P.concrete.sparsity.periodicSparsity.neighborSet L i) :
    (sigma4PeriodicFullRowStencil L).weight i j = 0 :=
  P.concrete.periodic_zeroOutside L hL hnot

theorem open_activeTargets_card_le_eighty_one
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.concrete.sparsity.openSparsity.activeTargets L i).card ≤ 81 :=
  P.concrete.open_activeTargets_card_le_eighty_one L hL i

theorem periodic_activeTargets_card_le_eighty_one
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (hL : 4 ≤ L) (i : SigmaCoord4 L) :
    (P.concrete.sparsity.periodicSparsity.activeTargets L i).card ≤ 81 :=
  P.concrete.periodic_activeTargets_card_le_eighty_one L hL i

theorem open_localRayleighNumerator_eq_nodeDot_laplacianMulVec
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    P.concrete.sparsity.openSparsity.localRayleighNumerator
        sigma4OpenFullRowStencilCenter L v =
      sigma4BlockStarOpenLaplacianFamily.nodeDot L v
        (sigma4BlockStarOpenLaplacianFamily.laplacianMulVec L v) := by
  exact sigma4OpenLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    P.concrete.sparsity.openSparsity L v

theorem periodic_localRayleighNumerator_eq_nodeDot_laplacianMulVec
    (P : Sigma4FirstPositiveBoundaryLocalSpectralProgram)
    (L : ℕ) (v : SigmaCoord4 L → ℝ) :
    P.concrete.sparsity.periodicSparsity.localRayleighNumerator
        sigma4PeriodicFullRowStencilCenter L v =
      sigma4PeriodicBlockStarLaplacianFamily.nodeDot L v
        (sigma4PeriodicBlockStarLaplacianFamily.laplacianMulVec L v) := by
  exact sigma4PeriodicLocalRayleighNumerator_eq_nodeDot_laplacianMulVec_of_sparsity
    P.concrete.sparsity.periodicSparsity L v

end Sigma4FirstPositiveBoundaryLocalSpectralProgram

namespace Sigma4FirstPositiveBoundaryContinuumLimitProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryContinuumLimitProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram where
  concrete := P.toSigma4ConcreteBoundarySpectralLimitProgramFrom.withSparsity
  periodicLambda_eq := rfl
  openLambda_eq := rfl
  periodicL0_eq := rfl
  openL0_eq := rfl

end Sigma4FirstPositiveBoundaryContinuumLimitProgram

namespace Sigma4FirstPositiveBoundaryErrorProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryErrorProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryErrorProgram

namespace Sigma4FirstPositiveBoundaryAbsErrorBoundProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryAbsErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryAbsErrorBoundProgram

namespace Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryInverseLinearErrorBoundProgram

namespace Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryCubicEigenvalueErrorBoundProgram

namespace Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryCubicSpectralBracketingProgram

namespace Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryRescaledSpectralBracketingProgram

namespace Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryExplicitRescaledSpectralBracketingProgram

namespace Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram

namespace Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toContinuumLimitProgram.toLocalSpectralProgram

end Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram

/--
First-positive Sigma4 boundary programme whose remaining analytic obligations
are stated as local sparse Rayleigh lower and upper certificates.
-/
structure Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram where
  bracketing :
    Sigma4BoundaryLocalRayleighContinuumSplitCertificate
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue

namespace Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram

noncomputable def toSplitEigenmodeRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram) :
    Sigma4FirstPositiveBoundarySplitEigenmodeRescaledSpectralBracketingProgram where
  bracketing := P.bracketing.toBoundaryContinuumSplitEigenmode

noncomputable def toEigenmodeRescaledSpectralBracketingProgram
    (P : Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram) :
    Sigma4FirstPositiveBoundaryEigenmodeRescaledSpectralBracketingProgram :=
  P.toSplitEigenmodeRescaledSpectralBracketingProgram
    |>.toEigenmodeRescaledSpectralBracketingProgram

noncomputable def toContinuumLimitProgram
    (P : Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram) :
    Sigma4FirstPositiveBoundaryContinuumLimitProgram :=
  P.toSplitEigenmodeRescaledSpectralBracketingProgram.toContinuumLimitProgram

noncomputable def toLocalSpectralProgram
    (P : Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram) :
    Sigma4FirstPositiveBoundaryLocalSpectralProgram :=
  P.toSplitEigenmodeRescaledSpectralBracketingProgram.toLocalSpectralProgram

theorem boundaryDifferenceInverseSquareBound
    (P : Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram) :
    BoundaryDifferenceInverseSquareBound
      sigma4PeriodicFirstPositiveSpectralValue
      sigma4OpenFirstPositiveSpectralValue
      P.toContinuumLimitProgram.differenceK
      P.toContinuumLimitProgram.differenceL0 := by
  exact P.toContinuumLimitProgram.boundaryDifferenceInverseSquareBound

end Sigma4FirstPositiveBoundaryLocalRayleighSplitProgram

noncomputable def sigmaBlockAverage4 (L : ℕ) (hL : 4 ≤ L)
    (κ : SigmaCurvatureField4 L) (c : SigmaCoord4 L) : ℝ :=
  ∑ e, blockAveragingMatrixFromSupports (sigmaBlockStarSupport4 L hL) c e * κ e

def sigmaNatAbsDiff (a b : ℕ) : ℕ :=
  (a - b) + (b - a)

def sigmaFinDistance {L : ℕ} (a b : Fin L) : ℕ :=
  sigmaNatAbsDiff a.val b.val

def sigmaCoord4L1Distance {L : ℕ} (a b : SigmaCoord4 L) : ℝ :=
  ((sigmaFinDistance a.1.1.1 b.1.1.1 +
      sigmaFinDistance a.1.1.2 b.1.1.2 +
        sigmaFinDistance a.1.2 b.1.2 +
          sigmaFinDistance a.2 b.2 : ℕ) : ℝ)

def sigmaFineEdgeEndpointDistance {L : ℕ}
    (e f : SigmaFineEdge4 L) : ℝ :=
  sigmaCoord4L1Distance (sigmaFineEdgeSource e) (sigmaFineEdgeSource f) +
    sigmaCoord4L1Distance (sigmaFineEdgeTarget e) (sigmaFineEdgeTarget f)

def sigmaBoolDistance (a b : Bool) : ℕ :=
  if a = b then 0 else 1

def sigmaFineEdgeTensionDistance {L : ℕ}
    (e f : SigmaFineEdge4 L) : ℝ :=
  sigmaFineEdgeEndpointDistance e f +
    (sigmaBoolDistance (sigmaFineEdgeForward e) (sigmaFineEdgeForward f) : ℝ)

lemma sigmaCoord4L1Distance_nonneg {L : ℕ} (a b : SigmaCoord4 L) :
    0 ≤ sigmaCoord4L1Distance a b := by
  unfold sigmaCoord4L1Distance
  positivity

lemma sigmaFineEdgeEndpointDistance_nonneg {L : ℕ}
    (e f : SigmaFineEdge4 L) :
    0 ≤ sigmaFineEdgeEndpointDistance e f := by
  unfold sigmaFineEdgeEndpointDistance
  exact add_nonneg
    (sigmaCoord4L1Distance_nonneg (sigmaFineEdgeSource e)
      (sigmaFineEdgeSource f))
    (sigmaCoord4L1Distance_nonneg (sigmaFineEdgeTarget e)
      (sigmaFineEdgeTarget f))

lemma sigmaBoolDistance_nonneg (a b : Bool) :
    0 ≤ (sigmaBoolDistance a b : ℝ) := by
  unfold sigmaBoolDistance
  split <;> norm_num

lemma sigmaFineEdgeTensionDistance_nonneg {L : ℕ}
    (e f : SigmaFineEdge4 L) :
    0 ≤ sigmaFineEdgeTensionDistance e f := by
  unfold sigmaFineEdgeTensionDistance
  exact add_nonneg
    (sigmaFineEdgeEndpointDistance_nonneg e f)
    (sigmaBoolDistance_nonneg (sigmaFineEdgeForward e)
      (sigmaFineEdgeForward f))

def sigmaCoord4Time {L : ℕ} (x : SigmaCoord4 L) : ℝ :=
  (x.1.1.1.val : ℝ) + (x.1.1.2.val : ℝ) +
    (x.1.2.val : ℝ) + (x.2.val : ℝ)

lemma sigmaCoord4Time_set {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (v : Fin L) :
    sigmaCoord4Time (sigmaCoord4Set x axis v) =
      sigmaCoord4Time x -
        (sigmaCoord4Get x axis).val + v.val := by
  fin_cases axis <;>
    simp [sigmaCoord4Time, sigmaCoord4Set, sigmaCoord4Get] <;>
      ring

def sigmaOrientationTension {L : ℕ} (e : SigmaFineEdge4 L) : ℝ :=
  if sigmaFineEdgeForward e then 1 else -1

lemma sigmaCoord4Time_target_sub_source {L : ℕ}
    (e : SigmaFineEdge4 L) :
    sigmaCoord4Time (sigmaFineEdgeTarget e) -
      sigmaCoord4Time (sigmaFineEdgeSource e) =
        sigmaOrientationTension e := by
  by_cases hf : sigmaFineEdgeForward e = true
  · rw [sigmaFineEdgeTarget, sigmaCoord4Time_set,
      sigmaFineEdgeStepTarget_val_forward e hf]
    simp [sigmaOrientationTension, hf]
    ring
  · have hfalse : sigmaFineEdgeForward e = false :=
      Bool.eq_false_of_not_eq_true hf
    have hsource_pos :
        0 < (sigmaCoord4Get (sigmaFineEdgeSource e)
          (sigmaFineEdgeAxis e)).val := by
      have hraw : e.1.2 = false := by
        simpa [sigmaFineEdgeForward] using hfalse
      simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using e.2
    have hcast :
        (((sigmaCoord4Get (sigmaFineEdgeSource e)
          (sigmaFineEdgeAxis e)).val - 1 : ℕ) : ℝ) =
          (sigmaCoord4Get (sigmaFineEdgeSource e)
            (sigmaFineEdgeAxis e)).val - 1 := by
      exact Nat.cast_pred hsource_pos
    rw [sigmaFineEdgeTarget, sigmaCoord4Time_set,
      sigmaFineEdgeStepTarget_val_backward e hfalse]
    rw [hcast]
    simp [sigmaOrientationTension, hfalse]

lemma sigmaOrientationTension_ne_zero {L : ℕ}
    (e : SigmaFineEdge4 L) :
    sigmaOrientationTension e ≠ 0 := by
  cases hf : sigmaFineEdgeForward e <;>
    simp [sigmaOrientationTension, hf]

lemma sigmaOrientationTension_reverse {L : ℕ}
    (e : SigmaFineEdge4 L) :
    sigmaOrientationTension (sigmaFineEdgeReverse e) =
      -sigmaOrientationTension e := by
  cases hf : sigmaFineEdgeForward e <;>
    simp [sigmaOrientationTension, sigmaFineEdgeReverse_forward, hf]

lemma sigmaOrientationTension_abs_sub_le_two {L : ℕ}
    (e f : SigmaFineEdge4 L) :
    |sigmaOrientationTension e - sigmaOrientationTension f| ≤ 2 := by
  cases he : sigmaFineEdgeForward e <;>
    cases hf : sigmaFineEdgeForward f <;>
      norm_num [sigmaOrientationTension, he, hf]

lemma sigmaOrientationTension_lipschitz {L : ℕ} :
    ∃ C : ℝ, 0 < C ∧
      ∀ e f : SigmaFineEdge4 L,
        |sigmaOrientationTension e - sigmaOrientationTension f| ≤
          C * sigmaFineEdgeTensionDistance e f := by
  refine ⟨2, by norm_num, ?_⟩
  intro e f
  by_cases hdir : sigmaFineEdgeForward e = sigmaFineEdgeForward f
  · have htension : sigmaOrientationTension e = sigmaOrientationTension f := by
      cases he : sigmaFineEdgeForward e <;>
        cases hf : sigmaFineEdgeForward f <;>
          simp_all [sigmaOrientationTension]
    rw [htension, sub_self, abs_zero]
    exact mul_nonneg (by norm_num) (sigmaFineEdgeTensionDistance_nonneg e f)
  · have hbool :
        ((sigmaBoolDistance (sigmaFineEdgeForward e)
          (sigmaFineEdgeForward f) : ℕ) : ℝ) = 1 := by
      simp [sigmaBoolDistance, hdir]
    have hdist : 1 ≤ sigmaFineEdgeTensionDistance e f := by
      unfold sigmaFineEdgeTensionDistance
      rw [hbool]
      nlinarith [sigmaFineEdgeEndpointDistance_nonneg e f]
    have habs := sigmaOrientationTension_abs_sub_le_two e f
    nlinarith

/-- Primitive positive time readout of a Sigma fine edge. -/
def sigmaPlanckPrimitiveTime4 {L : ℕ} (e : SigmaFineEdge4 L) : ℝ :=
  |sigmaCoord4Time (sigmaFineEdgeTarget e) -
    sigmaCoord4Time (sigmaFineEdgeSource e)|

lemma sigmaPlanckPrimitiveTime4_eq_one {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaPlanckPrimitiveTime4 e = 1 := by
  unfold sigmaPlanckPrimitiveTime4
  rw [sigmaCoord4Time_target_sub_source]
  cases hf : sigmaFineEdgeForward e <;>
    norm_num [sigmaOrientationTension, hf]

/-- Concrete sigma.P clock for the 4D block-star fine-edge model. -/
def sigma4PlanckNoZeroClock (L : ℕ) :
    SigmaPlanckNoZeroClock (SigmaFineEdge4 L) where
  planckUnit := 1
  planckUnit_pos := by
    norm_num
  primitiveTime := sigmaPlanckPrimitiveTime4
  primitiveTime_multiple := by
    intro e
    refine ⟨1, by norm_num, ?_⟩
    rw [sigmaPlanckPrimitiveTime4_eq_one e]
    norm_num

/--
Concrete Appendix VI source package: sigma.P supplies Planck-positive primitive
time readouts, and the 4D block-star template supplies connected finite
overlap supports.
-/
noncomputable def sigma4PlanckBlockStarSource (L : ℕ) (hL : 4 ≤ L) :
    SigmaPlanckBlockStarSource (SigmaCoord4 L) (SigmaFineEdge4 L) where
  clock := sigma4PlanckNoZeroClock L
  coarseGraph := sigmaCoarseGraph4 L
  fineEdgeSupport := sigmaBlockStarSupport4 L hL
  support_planck_nonempty := by
    intro c
    refine ⟨sigmaFineEdgeAtSource L hL c, ?_, ?_⟩
    · have hs := sigmaFineEdgeAtSource_source L hL c
      simp [sigmaBlockStarSupport4, hs,
        sigmaCoordInClosedTwoByTwoByTwoByTwoStar,
        cubeCoordInClosedTwoByTwoByTwoStar, coordInClosedTwoBlock]
    · exact SigmaPlanckNoZeroClock.primitiveTime_pos
        (sigma4PlanckNoZeroClock L) (sigmaFineEdgeAtSource L hL c)
  coarse_connected := sigmaCoarseGraph4_connected L hL
  adjacent_share_fine_edge := sigmaBlockStarSupport4_adjacent_inter_nonempty hL

theorem sigma4PlanckBlockStarSource_generates_covering
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ C : SigmaBlockStarCovering (SigmaCoord4 L) (SigmaFineEdge4 L),
      C.coarseGraph = sigmaCoarseGraph4 L ∧
        C.fineEdgeSupport = sigmaBlockStarSupport4 L hL := by
  refine ⟨(sigma4PlanckBlockStarSource L hL).toSigmaBlockStarCovering, ?_, ?_⟩
  · rfl
  · rfl

theorem sigma4PlanckBlockStarSource_blockLaplacian (L : ℕ) (hL : 4 ≤ L) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports (sigmaBlockStarSupport4 L hL)))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports (sigmaBlockStarSupport4 L hL)))),
          0 ≤ μ) ∧
        ∀ x : SigmaCoord4 L → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports
                (sigmaBlockStarSupport4 L hL)))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  simpa [sigma4PlanckBlockStarSource] using
    (SigmaPlanckBlockStarSource.blockLaplacian
      (sigma4PlanckBlockStarSource L hL))

theorem sigma4PlanckBlockStarSource_positive_spectral_gap
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports (sigmaBlockStarSupport4 L hL)))),
        μ ≠ 0 → γ ≤ μ := by
  simpa [sigma4PlanckBlockStarSource] using
    (SigmaPlanckBlockStarSource.positive_spectral_gap
      (sigma4PlanckBlockStarSource L hL))

/--
Source-grounded package for the physical Sigma axioms used before Appendix VI.

The source states these as axioms/postulates: directed tension with local scale
(sigma.1), non-zero finite tension (sigma.2), reversal antisymmetry (sigma.3),
and a Lipschitz-type continuity law (sigma.4).  Finiteness is automatic because
the field is real-valued.

The Planck/no-zero axiom sigma.P is formalized separately by
`SigmaPlanckNoZeroClock` and by the concrete source package
`sigma4PlanckBlockStarSource`.

This structure is the upstream Sigma-realisation layer for the block-star data.
The Appendix VI spectral argument below only uses the finite overlap operator
and its connectivity/locality properties once those data have been constructed.
Thus the physical axioms are retained here to document and formalize the Sigma
origin of the data, not because the purely finite-dimensional spectral lemmas
need them as additional algebraic hypotheses.
-/
structure SigmaPhysicalAxioms4 (L : ℕ) (hL : 4 ≤ L) where
  eventTime : SigmaCoord4 L → ℝ
  localScale : SigmaFineEdge4 L → ℝ
  tension : SigmaFineEdge4 L → ℝ
  edgeReverse : SigmaFineEdge4 L → SigmaFineEdge4 L
  reverse_source :
    ∀ e, sigmaFineEdgeSource (edgeReverse e) = sigmaFineEdgeTarget e
  reverse_target :
    ∀ e, sigmaFineEdgeTarget (edgeReverse e) = sigmaFineEdgeSource e
  sigma1_scale_pos :
    ∀ e, 0 < localScale e
  sigma1_tension_eq_time_div_scale :
    ∀ e,
      tension e =
        (eventTime (sigmaFineEdgeTarget e) -
            eventTime (sigmaFineEdgeSource e)) / localScale e
  sigma2_tension_nonzero :
    ∀ e, tension e ≠ 0
  sigma3_reverse_tension :
    ∀ e, tension (edgeReverse e) = -tension e
  sigma4_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ e f,
        |tension e - tension f| ≤
          C * sigmaFineEdgeTensionDistance e f

namespace SigmaPhysicalAxioms4

variable {L : ℕ} {hL : 4 ≤ L} (A : SigmaPhysicalAxioms4 L hL)

def curvatureField : SigmaCurvatureField4 L :=
  A.tension

noncomputable def blockAverage (c : SigmaCoord4 L) : ℝ :=
  sigmaBlockAverage4 L hL A.curvatureField c

lemma sigma1_future_positive {e : SigmaFineEdge4 L}
    (hfuture : A.eventTime (sigmaFineEdgeSource e) <
      A.eventTime (sigmaFineEdgeTarget e)) :
    0 < A.tension e := by
  rw [A.sigma1_tension_eq_time_div_scale e]
  exact div_pos (sub_pos.mpr hfuture) (A.sigma1_scale_pos e)

lemma sigma2_abs_pos (e : SigmaFineEdge4 L) :
    0 < |A.tension e| := by
  exact abs_pos.mpr (A.sigma2_tension_nonzero e)

lemma sigma3_reverse_reverse_tension (e : SigmaFineEdge4 L) :
    A.tension (A.edgeReverse (A.edgeReverse e)) = A.tension e := by
  rw [A.sigma3_reverse_tension, A.sigma3_reverse_tension]
  ring

theorem blockLaplacian :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (sigma4BlockStarCovering L hL).fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport))), 0 ≤ μ) ∧
        ∀ x : SigmaCoord4 L → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports
                (sigma4BlockStarCovering L hL).fineEdgeSupport))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact sigmaBlockStarCovering_blockLaplacian (sigma4BlockStarCovering L hL)

end SigmaPhysicalAxioms4

def concreteSigmaPhysicalAxioms4 (L : ℕ) (hL : 4 ≤ L) :
    SigmaPhysicalAxioms4 L hL where
  eventTime := sigmaCoord4Time
  localScale := fun _ => 1
  tension := sigmaOrientationTension
  edgeReverse := sigmaFineEdgeReverse
  reverse_source := sigmaFineEdgeReverse_source
  reverse_target := sigmaFineEdgeReverse_target
  sigma1_scale_pos := by
    intro e
    norm_num
  sigma1_tension_eq_time_div_scale := by
    intro e
    rw [sigmaCoord4Time_target_sub_source]
    norm_num
  sigma2_tension_nonzero := sigmaOrientationTension_ne_zero
  sigma3_reverse_tension := sigmaOrientationTension_reverse
  sigma4_lipschitz := sigmaOrientationTension_lipschitz

theorem sigmaPhysicalAxioms4_nonempty (L : ℕ) (hL : 4 ≤ L) :
    Nonempty (SigmaPhysicalAxioms4 L hL) :=
  ⟨concreteSigmaPhysicalAxioms4 L hL⟩

theorem concreteSigmaPhysicalAxioms4_blockLaplacian (L : ℕ) (hL : 4 ≤ L) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (sigma4BlockStarCovering L hL).fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport))), 0 ≤ μ) ∧
        ∀ x : SigmaCoord4 L → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports
                (sigma4BlockStarCovering L hL).fineEdgeSupport))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact SigmaPhysicalAxioms4.blockLaplacian
    (L := L) (hL := hL)

theorem concreteSigmaPhysicalAxioms4_positive_spectral_gap (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport))),
        μ ≠ 0 → γ ≤ μ := by
  exact sigmaBlockStarCovering_positive_spectral_gap (sigma4BlockStarCovering L hL)

theorem sigma4BlockStarCovering_blockLaplacian (L : ℕ) (hL : 4 ≤ L) :
    (similaritySymmetrizedLaplacian
      (coarseOverlapMatrix
        (blockAveragingMatrixFromSupports
          (sigma4BlockStarCovering L hL).fineEdgeSupport))).PosSemidef ∧
      (∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport))), 0 ≤ μ) ∧
        ∀ x : SigmaCoord4 L → ℝ,
          (randomWalkLaplacian
            (coarseOverlapMatrix
              (blockAveragingMatrixFromSupports
                (sigma4BlockStarCovering L hL).fineEdgeSupport))).mulVec x = 0 ↔
            ∃ c : ℝ, x = fun _ => c := by
  exact sigmaBlockStarCovering_blockLaplacian (sigma4BlockStarCovering L hL)

theorem sigma4BlockStarCovering_positive_spectral_gap (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ μ ∈ spectrum ℝ
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport))),
        μ ≠ 0 → γ ≤ μ := by
  exact sigmaBlockStarCovering_positive_spectral_gap (sigma4BlockStarCovering L hL)

theorem sigma4BlockStarCovering_modal_poincare_decay
    (L : ℕ) (hL : 4 ≤ L)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4BlockStarCovering L hL).fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalHeatEnergy μ t a ≤ Real.exp (-2 * γ * t) * modalEnergy a := by
  exact sigmaBlockStarCovering_modal_poincare_decay
    (sigma4BlockStarCovering L hL) μ hspec

theorem sigma4BlockStarCovering_diagonalHeatFlow_decay
    (L : ℕ) (hL : 4 ≤ L)
    {κ : Type*} [Fintype κ] (μ : κ → ℝ)
    (hspec : ∀ k, μ k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4BlockStarCovering L hL).fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ a : κ → ℝ, ReducedModalCoefficients μ a →
        γ * modalEnergy a ≤ modalDirichletEnergy μ a ∧
          ∀ t : ℝ, 0 ≤ t →
            modalEnergy (diagonalHeatFlow μ t a) ≤
              Real.exp (-2 * γ * t) * modalEnergy a := by
  exact sigmaBlockStarCovering_diagonalHeatFlow_decay
    (sigma4BlockStarCovering L hL) μ hspec

theorem sigma4BlockStarCovering_spectralFrame_heatFlow_decay
    (L : ℕ) (hL : 4 ≤ L)
    {κ : Type*} [Fintype κ]
    (F :
      MatrixSpectralFrame
        (randomWalkLaplacian
          (coarseOverlapMatrix
            (blockAveragingMatrixFromSupports
              (sigma4BlockStarCovering L hL).fineEdgeSupport)))
        κ)
    (hspec : ∀ k, F.freq k ∈ spectrum ℝ
      (randomWalkLaplacian
        (coarseOverlapMatrix
          (blockAveragingMatrixFromSupports
            (sigma4BlockStarCovering L hL).fineEdgeSupport)))) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ (SigmaCoord4 L),
        ReducedModalCoefficients F.freq (F.coords x) →
          γ * modalEnergy (F.coords x) ≤ modalDirichletEnergy F.freq (F.coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖F.heatFlow t x‖ ^ 2 ≤ Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  exact sigmaBlockStarCovering_spectralFrame_heatFlow_decay
    (sigma4BlockStarCovering L hL) F hspec

theorem sigma4BlockStarCovering_canonicalSymmetrizedHeatFlow_decay
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ γ : ℝ, 0 < γ ∧
      ∀ x : EuclideanSpace ℝ (SigmaCoord4 L),
        ReducedModalCoefficients
          (sigmaBlockStarCoveringSymmetrizedSpectralFrame
            (sigma4BlockStarCovering L hL)).freq
          ((sigmaBlockStarCoveringSymmetrizedSpectralFrame
            (sigma4BlockStarCovering L hL)).coords x) →
          γ * modalEnergy
              ((sigmaBlockStarCoveringSymmetrizedSpectralFrame
                (sigma4BlockStarCovering L hL)).coords x) ≤
              modalDirichletEnergy
                (sigmaBlockStarCoveringSymmetrizedSpectralFrame
                  (sigma4BlockStarCovering L hL)).freq
                ((sigmaBlockStarCoveringSymmetrizedSpectralFrame
                  (sigma4BlockStarCovering L hL)).coords x) ∧
            ∀ t : ℝ, 0 ≤ t →
              ‖(sigmaBlockStarCoveringSymmetrizedSpectralFrame
                (sigma4BlockStarCovering L hL)).heatFlow t x‖ ^ 2 ≤
                Real.exp (-2 * γ * t) * ‖x‖ ^ 2 := by
  exact sigmaBlockStarCovering_canonicalSymmetrizedHeatFlow_decay
    (sigma4BlockStarCovering L hL)

end Hardtest
