/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Mathlib

/-!
Source-grounded first Lean slice for
`emergent_gaugeV2_rewritten_paper.tex`.

This file formalizes the finite cochain transport core:

* exact shifts of a real Sigma 1-cochain,
* period invariance on closed 1-chains,
* abelian phase holonomy,
* the cellular Stokes identity for face holonomy.

The continuum representative-connection, path-ordered exponential, BCH remainder,
and photon/dynamical claims are intentionally not part of this first finite core.
-/

namespace Hardtest
namespace GaugeTransport

open scoped BigOperators

/-- A finite oriented transport complex, reduced to the incidence data needed for
the cochain-level gauge-transport identities. -/
structure FiniteTransportComplex (V E F : Type*) [Fintype E] [Fintype F] where
  source : E → V
  target : E → V
  faceBoundary : F → E → ℤ

namespace FiniteTransportComplex

variable {V E F : Type*} [Fintype E] [Fintype F]

/-- The exact 1-cochain `d λ` on an oriented edge. -/
def d0 (K : FiniteTransportComplex V E F) (lambda : V → ℝ) : E → ℝ :=
  fun e => lambda (K.target e) - lambda (K.source e)

/-- Exact-shift action on a real Sigma 1-cochain. -/
def exactShift (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) : E → ℝ :=
  fun e => sigma e + K.d0 lambda e

/-- Pairing of a real 1-cochain with an integral 1-chain. -/
def edgePairing (sigma : E → ℝ) (c : E → ℤ) : ℝ :=
  ∑ e, (c e : ℝ) * sigma e

/-- A closed 1-chain, characterized exactly by annihilating all exact 1-cochains. -/
def IsClosed1Chain (K : FiniteTransportComplex V E F) (c : E → ℤ) : Prop :=
  ∀ lambda : V → ℝ, edgePairing (K.d0 lambda) c = 0

/-- Coboundary of a real 1-cochain on faces. -/
def faceCoboundary (K : FiniteTransportComplex V E F) (sigma : E → ℝ) : F → ℝ :=
  fun f => ∑ e, (K.faceBoundary f e : ℝ) * sigma e

/-- Pairing of a real 2-cochain with an integral 2-chain. -/
def facePairing (omega : F → ℝ) (S : F → ℤ) : ℝ :=
  ∑ f, (S f : ℝ) * omega f

/-- Boundary of an integral 2-chain. -/
def boundary2 (K : FiniteTransportComplex V E F) (S : F → ℤ) : E → ℤ :=
  fun e => ∑ f, S f * K.faceBoundary f e

/-- Abelian phase associated with a real transport value. -/
noncomputable def phase (Lambda x : ℝ) : ℂ :=
  Complex.exp (Complex.I * ((x / Lambda : ℝ) : ℂ))

/-- Abelian holonomy phase of a 1-cochain along an integral 1-chain. -/
noncomputable def chainHolonomy (Lambda : ℝ) (sigma : E → ℝ) (c : E → ℤ) : ℂ :=
  phase Lambda (edgePairing sigma c)

/-- Abelian curvature phase of a 2-cochain on an integral 2-chain. -/
noncomputable def faceHolonomy (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (S : F → ℤ) : ℂ :=
  phase Lambda (facePairing (K.faceCoboundary sigma) S)

lemma phase_add (Lambda x y : ℝ) :
    phase Lambda (x + y) = phase Lambda x * phase Lambda y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  norm_num
  ring_nf

lemma phase_zero (Lambda : ℝ) :
    phase Lambda 0 = 1 := by
  simp [phase]

/-- Exact shifts act on a single link by the two endpoint phases. -/
theorem endpointPhaseAction (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (e : E) :
    phase Lambda (K.exactShift sigma lambda e) =
      phase Lambda (-(lambda (K.source e))) *
        phase Lambda (sigma e) *
          phase Lambda (lambda (K.target e)) := by
  have harg :
      K.exactShift sigma lambda e =
        -(lambda (K.source e)) + sigma e + lambda (K.target e) := by
    simp [exactShift, d0]
    ring
  rw [harg]
  rw [phase_add, phase_add]

/-- Periods over closed 1-chains are invariant under exact shifts. -/
theorem period_exactShift_invariant (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    edgePairing (K.exactShift sigma lambda) c = edgePairing sigma c := by
  calc
    edgePairing (K.exactShift sigma lambda) c
        = edgePairing sigma c + edgePairing (K.d0 lambda) c := by
          simp [edgePairing, exactShift, d0, Finset.sum_add_distrib, mul_add]
    _ = edgePairing sigma c := by
          simp [hclosed lambda]

/-- Closed-chain abelian holonomy depends only on the exact-shift class. -/
theorem closedChainHolonomy_exactShift_invariant
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda (K.exactShift sigma lambda) c =
      chainHolonomy Lambda sigma c := by
  simp [chainHolonomy, period_exactShift_invariant K sigma lambda c hclosed]

/-- Cellular Stokes: pairing with the boundary 2-chain equals pairing with the
cochain coboundary. -/
theorem discreteStokes_pairing (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (S : F → ℤ) :
    edgePairing sigma (K.boundary2 S) =
      facePairing (K.faceCoboundary sigma) S := by
  simp only [edgePairing, boundary2, facePairing, faceCoboundary, Int.cast_sum,
    Int.cast_mul]
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp [Finset.mul_sum, mul_left_comm, mul_comm]

/-- Exact discrete Stokes for abelian holonomy. -/
theorem discreteStokes_holonomy (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (S : F → ℤ) :
    chainHolonomy Lambda sigma (K.boundary2 S) =
      K.faceHolonomy Lambda sigma S := by
  simp [chainHolonomy, faceHolonomy, discreteStokes_pairing K sigma S]

/-! ### Finite reduced representatives -/

/-- Finite Euclidean pairing on real 1-cochains. -/
def edgeInner (alpha beta : E → ℝ) : ℝ :=
  ∑ e, alpha e * beta e

/-- Canonical `L²` realization of a finite real edge cochain as a Mathlib
Euclidean-space vector.  The surrounding development keeps the paper's
cochain notation `E → ℝ`; this bridge is only used to invoke orthogonal
projection in finite dimension. -/
noncomputable def edgeToEuclidean (alpha : E → ℝ) : EuclideanSpace ℝ E :=
  WithLp.toLp 2 alpha

/-- The Mathlib Euclidean inner product agrees with the finite edge pairing
used throughout this file. -/
lemma euclidean_inner_edgeToEuclidean (alpha beta : E → ℝ) :
    inner ℝ (edgeToEuclidean alpha) (edgeToEuclidean beta) =
      edgeInner alpha beta := by
  rw [show inner ℝ (edgeToEuclidean alpha) (edgeToEuclidean beta) =
    ∑ e, beta e * alpha e from rfl]
  unfold edgeInner
  exact Finset.sum_congr rfl (fun e _ => by ring)

/-- Squared finite Euclidean norm on real 1-cochains. -/
def edgeNormSq (alpha : E → ℝ) : ℝ :=
  edgeInner alpha alpha

/-- Reduced-representative quadratic energy in an exact-shift class. -/
noncomputable def reducedEnergy (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) : ℝ :=
  (1 / 2 : ℝ) * edgeNormSq (K.exactShift sigma lambda)

/-- A parameter is a reduced-energy minimizer if it minimizes over the full
finite exact-shift class. -/
def IsReducedEnergyMinimizer (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) : Prop :=
  ∀ mu : V → ℝ, K.reducedEnergy sigma lambda ≤ K.reducedEnergy sigma mu

/-- Finite normal equations for the reduced representative:
`d0 lambda` cancels the projection of `sigma` onto the exact subspace. -/
def SolvesReducedNormalEquations (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) : Prop :=
  ∀ eta : V → ℝ,
    edgeInner (K.d0 lambda) (K.d0 eta) =
      -edgeInner sigma (K.d0 eta)

/-- Solvability predicate for the reduced normal equations.  This is the finite
linear-algebra input behind unconditional existence of a reduced representative. -/
def ReducedNormalEquationsSolvable (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) : Prop :=
  ∃ lambda : V → ℝ, K.SolvesReducedNormalEquations sigma lambda

/-- The exact coboundary map, bundled as a linear map into Mathlib's finite
Euclidean edge space. -/
noncomputable def d0EuclideanLinear (K : FiniteTransportComplex V E F) :
    (V → ℝ) →ₗ[ℝ] EuclideanSpace ℝ E where
  toFun lambda := edgeToEuclidean (K.d0 lambda)
  map_add' lambda mu := by
    ext e
    simp [edgeToEuclidean, d0]
    ring
  map_smul' r lambda := by
    ext e
    simp [edgeToEuclidean, d0]
    ring

/-- Co-closedness written in adjoint-free finite form: the 1-cochain is
orthogonal to all exact 1-cochains.  With the standard finite inner product this
is the condition `d* sigma = 0`. -/
def IsCoClosed1Cochain (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) : Prop :=
  ∀ lambda : V → ℝ, edgeInner sigma (K.d0 lambda) = 0

/-- Closedness of a real 1-cochain under the cellular face coboundary. -/
def IsClosed1Cochain (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) : Prop :=
  K.faceCoboundary sigma = 0

/-- Harmonic 1-cochains are closed and co-closed in the finite cellular sense. -/
def IsHarmonic1Cochain (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) : Prop :=
  K.IsClosed1Cochain sigma ∧ K.IsCoClosed1Cochain sigma

/-- The cellular identity `d ∘ d = 0` for exact 1-cochains.  It is kept as an
explicit hypothesis because `FiniteTransportComplex` stores only incidence data. -/
def ExactOneCochainsClosed (K : FiniteTransportComplex V E F) : Prop :=
  ∀ lambda : V → ℝ, K.IsClosed1Cochain (K.d0 lambda)

/-- A reduced representative certificate for an exact-shift class. -/
structure ReducedRepresentative (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) where
  lambda : V → ℝ
  coClosed : K.IsCoClosed1Cochain (K.exactShift sigma lambda)

namespace ReducedRepresentative

variable (K : FiniteTransportComplex V E F) (sigma : E → ℝ)

/-- The actual co-closed representative carried by a certificate. -/
def representative (R : K.ReducedRepresentative sigma) : E → ℝ :=
  K.exactShift sigma R.lambda

end ReducedRepresentative

lemma edgeNormSq_nonneg (alpha : E → ℝ) :
    0 ≤ edgeNormSq alpha := by
  unfold edgeNormSq edgeInner
  exact Finset.sum_nonneg fun e _ => mul_self_nonneg (alpha e)

lemma edgeNormSq_eq_zero_iff (alpha : E → ℝ) :
    edgeNormSq alpha = 0 ↔ alpha = 0 := by
  constructor
  · intro h
    unfold edgeNormSq edgeInner at h
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg
      (fun e _ => mul_self_nonneg (alpha e))).mp h
    funext e
    exact mul_self_eq_zero.mp (hzero e (Finset.mem_univ e))
  · intro h
    simp [h, edgeNormSq, edgeInner]

lemma exactShift_add_parameter (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda eta : V → ℝ) :
    K.exactShift sigma (fun v => lambda v + eta v) =
      K.exactShift (K.exactShift sigma lambda) eta := by
  funext e
  simp [exactShift, d0]
  ring

lemma d0_smul (K : FiniteTransportComplex V E F)
    (r : ℝ) (eta : V → ℝ) :
    K.d0 (fun v => r * eta v) = fun e => r * K.d0 eta e := by
  funext e
  simp [d0]
  ring

lemma edgeInner_smul_right (alpha beta : E → ℝ) (r : ℝ) :
    edgeInner alpha (fun e => r * beta e) = r * edgeInner alpha beta := by
  unfold edgeInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro e _
  ring

lemma edgeNormSq_smul (beta : E → ℝ) (r : ℝ) :
    edgeNormSq (fun e => r * beta e) = r ^ 2 * edgeNormSq beta := by
  unfold edgeNormSq edgeInner
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl ?_
  intro e _
  ring

lemma edgeInner_add_left (alpha beta gamma : E → ℝ) :
    edgeInner (fun e => alpha e + beta e) gamma =
      edgeInner alpha gamma + edgeInner beta gamma := by
  unfold edgeInner
  simp [add_mul, Finset.sum_add_distrib]

lemma edgeInner_exactShift_left (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda eta : V → ℝ) :
    edgeInner (K.exactShift sigma lambda) (K.d0 eta) =
      edgeInner sigma (K.d0 eta) + edgeInner (K.d0 lambda) (K.d0 eta) := by
  change edgeInner (fun e => sigma e + K.d0 lambda e) (K.d0 eta) =
    edgeInner sigma (K.d0 eta) + edgeInner (K.d0 lambda) (K.d0 eta)
  exact edgeInner_add_left sigma (K.d0 lambda) (K.d0 eta)

lemma faceCoboundary_add (K : FiniteTransportComplex V E F)
    (alpha beta : E → ℝ) :
    K.faceCoboundary (fun e => alpha e + beta e) =
      fun f => K.faceCoboundary alpha f + K.faceCoboundary beta f := by
  funext f
  simp [faceCoboundary, mul_add, Finset.sum_add_distrib]

lemma faceCoboundary_exactShift (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) :
    K.faceCoboundary (K.exactShift sigma lambda) =
      fun f => K.faceCoboundary sigma f + K.faceCoboundary (K.d0 lambda) f := by
  funext f
  simp [faceCoboundary, exactShift, mul_add, Finset.sum_add_distrib]

lemma exactShift_closed_of_closed (K : FiniteTransportComplex V E F)
    (hdd : K.ExactOneCochainsClosed) (sigma : E → ℝ) (lambda : V → ℝ)
    (hclosed : K.IsClosed1Cochain sigma) :
    K.IsClosed1Cochain (K.exactShift sigma lambda) := by
  rw [IsClosed1Cochain, faceCoboundary_exactShift]
  funext f
  have hs := congrFun hclosed f
  have hd := congrFun (hdd lambda) f
  simp [hs, hd]

lemma edgeNormSq_exactShift_expand (K : FiniteTransportComplex V E F)
    (tau : E → ℝ) (eta : V → ℝ) :
    edgeNormSq (K.exactShift tau eta) =
      edgeNormSq tau + 2 * edgeInner tau (K.d0 eta) +
        edgeNormSq (K.d0 eta) := by
  unfold edgeNormSq edgeInner exactShift
  simp only [Finset.sum_add_distrib, add_mul, mul_add]
  have hcomm :
      (∑ x, K.d0 eta x * tau x) =
        ∑ x, tau x * K.d0 eta x := by
    refine Finset.sum_congr rfl ?_
    intro x _
    ring
  rw [hcomm]
  ring_nf

lemma reducedEnergy_add_parameter (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda eta : V → ℝ) :
    K.reducedEnergy sigma (fun v => lambda v + eta v) =
      (1 / 2 : ℝ) *
        (edgeNormSq (K.exactShift sigma lambda) +
          2 * edgeInner (K.exactShift sigma lambda) (K.d0 eta) +
            edgeNormSq (K.d0 eta)) := by
  rw [reducedEnergy, exactShift_add_parameter]
  rw [edgeNormSq_exactShift_expand]

lemma reducedEnergy_add_scaled_parameter (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda eta : V → ℝ) (r : ℝ) :
    K.reducedEnergy sigma (fun v => lambda v + r * eta v) =
      K.reducedEnergy sigma lambda +
        r * edgeInner (K.exactShift sigma lambda) (K.d0 eta) +
          (1 / 2 : ℝ) * (r ^ 2 * edgeNormSq (K.d0 eta)) := by
  rw [reducedEnergy_add_parameter]
  unfold reducedEnergy
  rw [d0_smul, edgeInner_smul_right, edgeNormSq_smul]
  ring

/-- The co-closed Euler condition gives the least-norm representative in the
exact-shift class, in the finite algebraic form used by the paper. -/
theorem coClosed_reducedEnergy_le_add_parameter
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (lambda eta : V → ℝ)
    (hco : K.IsCoClosed1Cochain (K.exactShift sigma lambda)) :
    K.reducedEnergy sigma lambda ≤
      K.reducedEnergy sigma (fun v => lambda v + eta v) := by
  rw [reducedEnergy_add_parameter]
  unfold reducedEnergy
  have hcross : edgeInner (K.exactShift sigma lambda) (K.d0 eta) = 0 := hco eta
  have hnorm : 0 ≤ edgeNormSq (K.d0 eta) := edgeNormSq_nonneg (K.d0 eta)
  rw [hcross]
  nlinarith

/-- The quadratic first-variation coefficient vanishes if a nonnegative quadratic
variation is minimized at the origin. -/
lemma linear_coefficient_eq_zero_of_quadratic_nonneg
    (a b : ℝ) (hb : 0 ≤ b)
    (hquad : ∀ r : ℝ, 0 ≤ r * a + (1 / 2 : ℝ) * (r ^ 2 * b)) :
    a = 0 := by
  by_cases hbzero : b = 0
  · have hpos := hquad 1
    have hneg := hquad (-1)
    rw [hbzero] at hpos hneg
    norm_num at hpos hneg
    linarith
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    have hbne : b ≠ 0 := ne_of_gt hbpos
    have hineq := hquad (-a / b)
    have hcalc :
        (-a / b) * a + (1 / 2 : ℝ) * (((-a / b) ^ 2) * b) =
          -(a ^ 2) / (2 * b) := by
      field_simp [hbne]
      ring
    rw [hcalc] at hineq
    have hdenpos : 0 < 2 * b := by positivity
    have hmul := mul_nonneg hineq (le_of_lt hdenpos)
    have hprod : (-(a ^ 2) / (2 * b)) * (2 * b) = -(a ^ 2) := by
      field_simp [ne_of_gt hdenpos]
    have hsq_nonpos : 0 ≤ -(a ^ 2) := by
      simpa [hprod] using hmul
    nlinarith [sq_nonneg a]

/-- A global reduced-energy minimizer satisfies the co-closed Euler condition. -/
theorem coClosed_of_reducedEnergy_minimizer
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) (lambda : V → ℝ)
    (hmin : K.IsReducedEnergyMinimizer sigma lambda) :
    K.IsCoClosed1Cochain (K.exactShift sigma lambda) := by
  intro eta
  have hquad :
      ∀ r : ℝ, 0 ≤
        r * edgeInner (K.exactShift sigma lambda) (K.d0 eta) +
          (1 / 2 : ℝ) * (r ^ 2 * edgeNormSq (K.d0 eta)) := by
    intro r
    have hminr := hmin (fun v => lambda v + r * eta v)
    rw [reducedEnergy_add_scaled_parameter] at hminr
    nlinarith
  exact linear_coefficient_eq_zero_of_quadratic_nonneg
    (edgeInner (K.exactShift sigma lambda) (K.d0 eta))
    (edgeNormSq (K.d0 eta)) (edgeNormSq_nonneg (K.d0 eta)) hquad

/-- Co-closedness gives a global reduced-energy minimizer over the exact-shift
class. -/
theorem reducedEnergy_minimizer_of_coClosed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) (lambda : V → ℝ)
    (hco : K.IsCoClosed1Cochain (K.exactShift sigma lambda)) :
    K.IsReducedEnergyMinimizer sigma lambda := by
  intro mu
  let eta : V → ℝ := fun v => mu v - lambda v
  have hmu : mu = fun v => lambda v + eta v := by
    funext v
    simp [eta]
  rw [hmu]
  exact coClosed_reducedEnergy_le_add_parameter K sigma lambda eta hco

/-- Finite Euler--Lagrange form of the reduced-representative proposition:
minimizers in an exact-shift class are exactly the co-closed representatives. -/
theorem reducedEnergy_minimizer_iff_coClosed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) (lambda : V → ℝ) :
    K.IsReducedEnergyMinimizer sigma lambda ↔
      K.IsCoClosed1Cochain (K.exactShift sigma lambda) :=
  ⟨coClosed_of_reducedEnergy_minimizer K sigma lambda,
    reducedEnergy_minimizer_of_coClosed K sigma lambda⟩

/-- The finite normal equations are exactly the co-closed Euler equations for
the shifted representative. -/
theorem normalEquations_iff_coClosed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) (lambda : V → ℝ) :
    K.SolvesReducedNormalEquations sigma lambda ↔
      K.IsCoClosed1Cochain (K.exactShift sigma lambda) := by
  constructor
  · intro hnormal eta
    rw [edgeInner_exactShift_left]
    rw [hnormal eta]
    ring
  · intro hco eta
    have h := hco eta
    rw [edgeInner_exactShift_left] at h
    linarith

/-- A solution of the normal equations gives a concrete reduced representative. -/
def reducedRepresentativeOfNormalEquations
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) (lambda : V → ℝ)
    (hnormal : K.SolvesReducedNormalEquations sigma lambda) :
    K.ReducedRepresentative sigma where
  lambda := lambda
  coClosed := (normalEquations_iff_coClosed K sigma lambda).mp hnormal

/-- Normal-equation solvability yields existence of a reduced representative. -/
theorem exists_reducedRepresentative_of_normalEquations
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (hsol : K.ReducedNormalEquationsSolvable sigma) :
    ∃ R : K.ReducedRepresentative sigma, K.IsReducedEnergyMinimizer sigma R.lambda := by
  rcases hsol with ⟨lambda, hnormal⟩
  let R := reducedRepresentativeOfNormalEquations K sigma lambda hnormal
  exact ⟨R, reducedEnergy_minimizer_of_coClosed K sigma R.lambda R.coClosed⟩

/-- Reduced-representative existence is equivalent to finite normal-equation
solvability.  This isolates the remaining linear solver from the gauge proof. -/
theorem reducedRepresentative_exists_iff_normalEquationsSolvable
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    Nonempty (K.ReducedRepresentative sigma) ↔
      K.ReducedNormalEquationsSolvable sigma := by
  constructor
  · intro hR
    rcases hR with ⟨R⟩
    exact ⟨R.lambda, (normalEquations_iff_coClosed K sigma R.lambda).mpr R.coClosed⟩
  · intro hsol
    rcases exists_reducedRepresentative_of_normalEquations K sigma hsol with ⟨R, _⟩
    exact ⟨R⟩

/-- In the finite edge setting, the reduced normal equations are solvable for
every real 1-cochain.  The proof is the finite-dimensional orthogonal projection
of `-sigma` onto the exact subspace `range d0`. -/
theorem reducedNormalEquationsSolvable
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    K.ReducedNormalEquationsSolvable sigma := by
  let S : Submodule ℝ (EuclideanSpace ℝ E) := LinearMap.range K.d0EuclideanLinear
  let v : EuclideanSpace ℝ E := -edgeToEuclidean sigma
  let p : S := S.orthogonalProjection v
  have hp_mem : (p : EuclideanSpace ℝ E) ∈ LinearMap.range K.d0EuclideanLinear := p.2
  rcases hp_mem with ⟨lambda, hlambda⟩
  refine ⟨lambda, ?_⟩
  intro eta
  have heta_mem : K.d0EuclideanLinear eta ∈ S := ⟨eta, rfl⟩
  have horth_mem : v - (p : EuclideanSpace ℝ E) ∈ Sᗮ := by
    simp [p]
  have horth :
      inner ℝ (v - (p : EuclideanSpace ℝ E)) (K.d0EuclideanLinear eta) = 0 := by
    exact (Submodule.mem_orthogonal' S
      (v - (p : EuclideanSpace ℝ E))).mp horth_mem _ heta_mem
  rw [← hlambda] at horth
  rw [inner_sub_left] at horth
  change inner ℝ (-edgeToEuclidean sigma) (edgeToEuclidean (K.d0 eta)) -
      inner ℝ (edgeToEuclidean (K.d0 lambda))
        (edgeToEuclidean (K.d0 eta)) = 0 at horth
  rw [inner_neg_left] at horth
  rw [euclidean_inner_edgeToEuclidean, euclidean_inner_edgeToEuclidean] at horth
  linarith

/-- Every finite exact-shift class has a reduced representative, and the carried
representative minimizes the quadratic reduced energy. -/
theorem exists_reducedRepresentative
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    ∃ R : K.ReducedRepresentative sigma,
      K.IsReducedEnergyMinimizer sigma R.lambda :=
  exists_reducedRepresentative_of_normalEquations K sigma
    (reducedNormalEquationsSolvable K sigma)

/-- Nonempty form of reduced-representative existence. -/
theorem nonempty_reducedRepresentative
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    Nonempty (K.ReducedRepresentative sigma) := by
  rcases exists_reducedRepresentative K sigma with ⟨R, _⟩
  exact ⟨R⟩

/-- A reduced representative certificate produces an energy minimizer for every
finite exact variation. -/
theorem ReducedRepresentative.energy_minimizing
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (R : K.ReducedRepresentative sigma) (eta : V → ℝ) :
    K.reducedEnergy sigma R.lambda ≤
      K.reducedEnergy sigma (fun v => R.lambda v + eta v) :=
  coClosed_reducedEnergy_le_add_parameter K sigma R.lambda eta R.coClosed

/-- If the complex has `d ∘ d = 0` and the original cochain is closed, then every
co-closed exact-shift representative is harmonic. -/
theorem ReducedRepresentative.harmonic_of_closed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (R : K.ReducedRepresentative sigma)
    (hdd : K.ExactOneCochainsClosed) (hclosed : K.IsClosed1Cochain sigma) :
    K.IsHarmonic1Cochain (R.representative K sigma) :=
  ⟨exactShift_closed_of_closed K hdd sigma R.lambda hclosed, R.coClosed⟩

/-- A closed finite 1-cochain admits a harmonic reduced representative once the
stored incidence data satisfy the cellular identity `d ∘ d = 0`. -/
theorem exists_harmonicReducedRepresentative_of_closed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (hdd : K.ExactOneCochainsClosed) (hclosed : K.IsClosed1Cochain sigma) :
    ∃ R : K.ReducedRepresentative sigma,
      K.IsReducedEnergyMinimizer sigma R.lambda ∧
        K.IsHarmonic1Cochain (R.representative K sigma) := by
  rcases exists_reducedRepresentative K sigma with ⟨R, hmin⟩
  exact ⟨R, hmin, R.harmonic_of_closed K sigma hdd hclosed⟩

/-- Two co-closed representatives in the same exact-shift class coincide.  This is
the finite uniqueness core behind the harmonic uniqueness statement. -/
theorem coClosed_exactShift_unique
    (K : FiniteTransportComplex V E F) (tau₁ tau₂ : E → ℝ) (lambda : V → ℝ)
    (hrel : tau₁ = K.exactShift tau₂ lambda)
    (hco₁ : K.IsCoClosed1Cochain tau₁)
    (hco₂ : K.IsCoClosed1Cochain tau₂) :
    tau₁ = tau₂ := by
  have hnorm : edgeNormSq (K.d0 lambda) = 0 := by
    have h₁ : edgeInner tau₁ (K.d0 lambda) = 0 := hco₁ lambda
    have h₂ : edgeInner tau₂ (K.d0 lambda) = 0 := hco₂ lambda
    rw [hrel] at h₁
    unfold edgeInner exactShift at h₁
    simp only [add_mul, Finset.sum_add_distrib] at h₁
    unfold edgeInner at h₂
    have hsum : ∑ x, K.d0 lambda x * K.d0 lambda x = 0 := by
      nlinarith
    simpa [edgeNormSq, edgeInner] using hsum
  have hd0 : K.d0 lambda = 0 := (edgeNormSq_eq_zero_iff (K.d0 lambda)).mp hnorm
  rw [hrel]
  funext e
  simp [exactShift, hd0]

/-- Harmonic representatives are unique inside an exact-shift class.  Closedness
is included to match the paper statement; the proof only needs co-closedness. -/
theorem harmonic_exactShift_unique
    (K : FiniteTransportComplex V E F) (tau₁ tau₂ : E → ℝ) (lambda : V → ℝ)
    (hrel : tau₁ = K.exactShift tau₂ lambda)
    (hh₁ : K.IsHarmonic1Cochain tau₁)
    (hh₂ : K.IsHarmonic1Cochain tau₂) :
    tau₁ = tau₂ :=
  coClosed_exactShift_unique K tau₁ tau₂ lambda hrel hh₁.2 hh₂.2

/-! ### Paper-facing finite transport core names -/

/-- Paper-facing endpoint phase action for exact shifts of abelian link
transport. -/
theorem finiteExactShiftEndpointPhaseAction
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (e : E) :
    phase Lambda (K.exactShift sigma lambda e) =
      phase Lambda (-(lambda (K.source e))) *
        phase Lambda (sigma e) *
          phase Lambda (lambda (K.target e)) :=
  endpointPhaseAction K Lambda sigma lambda e

/-- Paper-facing exact-shift invariance of abelian holonomy on closed
1-chains. -/
theorem finiteClosedChainHolonomyExactShiftInvariant
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda (K.exactShift sigma lambda) c =
      chainHolonomy Lambda sigma c :=
  closedChainHolonomy_exactShift_invariant K Lambda sigma lambda c hclosed

/-- Paper-facing exact-shift invariance of periods on closed 1-chains. -/
theorem finitePeriodExactShiftInvariant
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (lambda : V → ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    edgePairing (K.exactShift sigma lambda) c = edgePairing sigma c :=
  period_exactShift_invariant K sigma lambda c hclosed

/-- Paper-facing finite cellular Stokes identity for pairings. -/
theorem finiteDiscreteStokesPairing
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (S : F → ℤ) :
    edgePairing sigma (K.boundary2 S) =
      facePairing (K.faceCoboundary sigma) S :=
  discreteStokes_pairing K sigma S

/-- Paper-facing period difference for homologous finite 1-chains. -/
theorem finiteBoundaryPeriodDifference
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (c c' : E → ℤ) (S : F → ℤ)
    (hboundary : c - c' = K.boundary2 S) :
    edgePairing sigma c - edgePairing sigma c' =
      facePairing (K.faceCoboundary sigma) S := by
  calc
    edgePairing sigma c - edgePairing sigma c' =
        edgePairing sigma (c - c') := by
          simp [edgePairing, sub_mul, Finset.sum_sub_distrib]
    _ = facePairing (K.faceCoboundary sigma) S := by
          rw [hboundary]
          exact finiteDiscreteStokesPairing K sigma S

/-- Paper-facing homology invariance of periods for closed finite
1-cochains. -/
theorem finiteClosedCochainHomologyPeriodInvariant
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (c c' : E → ℤ) (S : F → ℤ)
    (hboundary : c - c' = K.boundary2 S)
    (hclosed : K.IsClosed1Cochain sigma) :
    edgePairing sigma c = edgePairing sigma c' := by
  have hdiff := finiteBoundaryPeriodDifference K sigma c c' S hboundary
  have hface : facePairing (K.faceCoboundary sigma) S = 0 := by
    rw [hclosed]
    simp [facePairing]
  linarith

/-- Paper-facing finite discrete Stokes theorem for abelian face holonomy. -/
theorem finiteDiscreteStokesHolonomy
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (S : F → ℤ) :
    chainHolonomy Lambda sigma (K.boundary2 S) =
      K.faceHolonomy Lambda sigma S :=
  discreteStokes_holonomy K Lambda sigma S

/-- Paper-facing existence of a reduced representative in every finite
exact-shift class. -/
theorem finiteReducedRepresentativeExists
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    ∃ R : K.ReducedRepresentative sigma,
      K.IsReducedEnergyMinimizer sigma R.lambda :=
  exists_reducedRepresentative K sigma

/-- Paper-facing uniqueness core for co-closed representatives in one
exact-shift class. -/
theorem finiteCoClosedRepresentativeUnique
    (K : FiniteTransportComplex V E F) (tau₁ tau₂ : E → ℝ) (lambda : V → ℝ)
    (hrel : tau₁ = K.exactShift tau₂ lambda)
    (hco₁ : K.IsCoClosed1Cochain tau₁)
    (hco₂ : K.IsCoClosed1Cochain tau₂) :
    tau₁ = tau₂ :=
  coClosed_exactShift_unique K tau₁ tau₂ lambda hrel hco₁ hco₂

/-- Paper-facing existence of a harmonic reduced representative for closed
finite 1-cochains when the incidence data satisfy `d ∘ d = 0`. -/
theorem finiteHarmonicReducedRepresentativeExists
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (hdd : K.ExactOneCochainsClosed) (hclosed : K.IsClosed1Cochain sigma) :
    ∃ R : K.ReducedRepresentative sigma,
      K.IsReducedEnergyMinimizer sigma R.lambda ∧
        K.IsHarmonic1Cochain (R.representative K sigma) :=
  exists_harmonicReducedRepresentative_of_closed K sigma hdd hclosed

/-- Paper-facing uniqueness of harmonic representatives in a fixed exact-shift
class. -/
theorem finiteHarmonicRepresentativeUnique
    (K : FiniteTransportComplex V E F) (tau₁ tau₂ : E → ℝ) (lambda : V → ℝ)
    (hrel : tau₁ = K.exactShift tau₂ lambda)
    (hh₁ : K.IsHarmonic1Cochain tau₁)
    (hh₂ : K.IsHarmonic1Cochain tau₂) :
    tau₁ = tau₂ :=
  harmonic_exactShift_unique K tau₁ tau₂ lambda hrel hh₁ hh₂

/-! ### Finite rooted path potentials -/

/-- A finite edge list is a path from `vStart` to `vEnd` when every edge starts
at the current vertex and the final current vertex is `vEnd`. -/
def IsEdgePathFrom (K : FiniteTransportComplex V E F)
    (vStart : V) : List E → V → Prop
  | [], vEnd => vEnd = vStart
  | e :: rest, vEnd => K.source e = vStart ∧ K.IsEdgePathFrom (K.target e) rest vEnd

/-- A finite edge list is a closed loop based at `base`. -/
def IsClosedEdgeLoop (K : FiniteTransportComplex V E F)
    (base : V) (edges : List E) : Prop :=
  K.IsEdgePathFrom base edges base

/-- Extending a finite source-target path by one outgoing edge gives a path to
that edge's target. -/
theorem isEdgePathFrom_snoc
    (K : FiniteTransportComplex V E F) {vStart : V} {edges : List E} {e : E}
    (hpath : K.IsEdgePathFrom vStart edges (K.source e)) :
    K.IsEdgePathFrom vStart (edges ++ [e]) (K.target e) := by
  induction edges generalizing vStart with
  | nil =>
      change K.source e = vStart ∧ K.target e = K.target e
      exact ⟨hpath, rfl⟩
  | cons first rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      simp [IsEdgePathFrom, hsource, ih htail]

/-- Integral of a real edge cochain along a finite oriented edge list. -/
def pathIntegral (sigma : E → ℝ) : List E → ℝ
  | [] => 0
  | e :: rest => sigma e + pathIntegral sigma rest

omit [Fintype E] in
/-- Path integrals are additive under concatenation. -/
lemma pathIntegral_append (sigma : E → ℝ) (edges₁ edges₂ : List E) :
    pathIntegral sigma (edges₁ ++ edges₂) =
      pathIntegral sigma edges₁ + pathIntegral sigma edges₂ := by
  induction edges₁ with
  | nil =>
      simp [pathIntegral]
  | cons e rest ih =>
      simp [pathIntegral, ih, add_assoc]

omit [Fintype E] in
/-- Appending one edge adds its sigma value to the path integral. -/
lemma pathIntegral_append_singleton (sigma : E → ℝ) (edges : List E) (e : E) :
    pathIntegral sigma (edges ++ [e]) =
      pathIntegral sigma edges + sigma e := by
  simp [pathIntegral_append, pathIntegral]

/-- A signed traversal of an oriented edge.  `forward = true` traverses
`source → target`; `forward = false` traverses the same edge backwards. -/
structure SignedEdgeStep (E : Type*) where
  edge : E
  forward : Bool

namespace SignedEdgeStep

/-- Initial vertex of a signed edge traversal. -/
def source (K : FiniteTransportComplex V E F) (s : SignedEdgeStep E) : V :=
  if s.forward then K.source s.edge else K.target s.edge

/-- Terminal vertex of a signed edge traversal. -/
def target (K : FiniteTransportComplex V E F) (s : SignedEdgeStep E) : V :=
  if s.forward then K.target s.edge else K.source s.edge

/-- Signed contribution of one edge traversal to a real path integral. -/
def value (sigma : E → ℝ) (s : SignedEdgeStep E) : ℝ :=
  if s.forward then sigma s.edge else -sigma s.edge

end SignedEdgeStep

/-- The forward traversal of an oriented edge. -/
def signedForwardStep (e : E) : SignedEdgeStep E where
  edge := e
  forward := true

/-- The backward traversal of an oriented edge. -/
def signedBackwardStep (e : E) : SignedEdgeStep E where
  edge := e
  forward := false

/-- A signed finite edge list is a path from `vStart` to `vEnd` when each signed
step starts at the current vertex. -/
def IsSignedPathFrom (K : FiniteTransportComplex V E F)
    (vStart : V) : List (SignedEdgeStep E) → V → Prop
  | [], vEnd => vEnd = vStart
  | step :: rest, vEnd =>
      SignedEdgeStep.source K step = vStart ∧
        IsSignedPathFrom K (SignedEdgeStep.target K step) rest vEnd

/-- A signed finite edge list is a closed loop based at `base`. -/
def IsClosedSignedLoop (K : FiniteTransportComplex V E F)
    (base : V) (steps : List (SignedEdgeStep E)) : Prop :=
  IsSignedPathFrom K base steps base

/-- Path integral over a signed finite edge list. -/
def signedPathIntegral (sigma : E → ℝ) : List (SignedEdgeStep E) → ℝ
  | [] => 0
  | step :: rest => SignedEdgeStep.value sigma step + signedPathIntegral sigma rest

/-- Certificate that a signed finite loop is the boundary of a finite 2-chain,
expressed at the level of pairings.  This avoids committing to a concrete
multiset/counting representation of signed edge lists. -/
def SignedPathBoundsBy2Chain (K : FiniteTransportComplex V E F)
    (steps : List (SignedEdgeStep E)) : Prop :=
  ∃ S : F → ℤ, ∀ sigma : E → ℝ,
    signedPathIntegral sigma steps = edgePairing sigma (K.boundary2 S)

/-- If a signed path is certified as a 2-chain boundary, then every closed
finite 1-cochain has zero integral over it. -/
theorem signedPathIntegral_eq_zero_of_boundsBy2Chain_of_closed
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (steps : List (SignedEdgeStep E))
    (hbounds : SignedPathBoundsBy2Chain K steps)
    (hclosed : K.IsClosed1Cochain sigma) :
    signedPathIntegral sigma steps = 0 := by
  rcases hbounds with ⟨S, hS⟩
  rw [hS sigma]
  rw [discreteStokes_pairing K sigma S]
  rw [hclosed]
  simp [facePairing]

/-- Convert an ordinary oriented edge path to a signed forward path. -/
def signedForwardPath : List E → List (SignedEdgeStep E)
  | [] => []
  | e :: rest => signedForwardStep e :: signedForwardPath rest

/-- Reverse an ordinary oriented edge path as a signed backward path. -/
def signedReversePath : List E → List (SignedEdgeStep E)
  | [] => []
  | e :: rest => signedReversePath rest ++ [signedBackwardStep e]

omit [Fintype E] in
/-- Signed path integrals are additive under concatenation. -/
lemma signedPathIntegral_append
    (sigma : E → ℝ) (steps₁ steps₂ : List (SignedEdgeStep E)) :
    signedPathIntegral sigma (steps₁ ++ steps₂) =
      signedPathIntegral sigma steps₁ + signedPathIntegral sigma steps₂ := by
  induction steps₁ with
  | nil =>
      simp [signedPathIntegral]
  | cons step rest ih =>
      simp [signedPathIntegral, ih, add_assoc]

omit [Fintype E] in
/-- Integral of the signed forward path is the ordinary path integral. -/
lemma signedPathIntegral_forwardPath (sigma : E → ℝ) (edges : List E) :
    signedPathIntegral sigma (signedForwardPath edges) = pathIntegral sigma edges := by
  induction edges with
  | nil =>
      simp [signedForwardPath, signedPathIntegral, pathIntegral]
  | cons e rest ih =>
      simp [signedForwardPath, signedForwardStep, signedPathIntegral,
        SignedEdgeStep.value, pathIntegral, ih]

omit [Fintype E] in
/-- Integral of the signed reverse path is minus the ordinary path integral. -/
lemma signedPathIntegral_reversePath (sigma : E → ℝ) (edges : List E) :
    signedPathIntegral sigma (signedReversePath edges) = -pathIntegral sigma edges := by
  induction edges with
  | nil =>
      simp [signedReversePath, signedPathIntegral, pathIntegral]
  | cons e rest ih =>
      simp [signedReversePath, signedPathIntegral_append, signedBackwardStep,
        signedPathIntegral, SignedEdgeStep.value, pathIntegral, ih]

/-- A source-target edge path is also a signed forward path. -/
theorem signedForwardPath_valid
    (K : FiniteTransportComplex V E F) {vStart vEnd : V} {edges : List E}
    (hpath : K.IsEdgePathFrom vStart edges vEnd) :
    IsSignedPathFrom K vStart (signedForwardPath edges) vEnd := by
  induction edges generalizing vStart with
  | nil =>
      simpa [IsEdgePathFrom, signedForwardPath, IsSignedPathFrom] using hpath
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      simp [signedForwardPath, signedForwardStep, IsSignedPathFrom,
        SignedEdgeStep.source, SignedEdgeStep.target, hsource, ih htail]

/-- Concatenating signed paths concatenates their endpoints. -/
theorem isSignedPathFrom_append
    (K : FiniteTransportComplex V E F)
    {v₀ v₁ v₂ : V} {steps₁ steps₂ : List (SignedEdgeStep E)}
    (h₁ : IsSignedPathFrom K v₀ steps₁ v₁)
    (h₂ : IsSignedPathFrom K v₁ steps₂ v₂) :
    IsSignedPathFrom K v₀ (steps₁ ++ steps₂) v₂ := by
  induction steps₁ generalizing v₀ with
  | nil =>
      simp [IsSignedPathFrom] at h₁
      simpa [h₁] using h₂
  | cons step rest ih =>
      rcases h₁ with ⟨hsource, htail⟩
      exact ⟨hsource, ih htail⟩

/-- Reversing an ordinary source-target path gives a valid signed backward
path. -/
theorem signedReversePath_valid
    (K : FiniteTransportComplex V E F) {vStart vEnd : V} {edges : List E}
    (hpath : K.IsEdgePathFrom vStart edges vEnd) :
    IsSignedPathFrom K vEnd (signedReversePath edges) vStart := by
  induction edges generalizing vStart with
  | nil =>
      simp [IsEdgePathFrom] at hpath
      simp [signedReversePath, IsSignedPathFrom, hpath.symm]
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      have hrev := ih htail
      have hstep :
          IsSignedPathFrom K (K.target e) [signedBackwardStep e] vStart := by
        simp [IsSignedPathFrom, signedBackwardStep, SignedEdgeStep.source,
          SignedEdgeStep.target, hsource.symm]
      simpa [signedReversePath] using isSignedPathFrom_append K hrev hstep

/-- A rooted path tree chooses one finite source-target path from a root to
every vertex.  This is finite combinatorial data; no smooth geometry is used. -/
structure RootedPathTree (K : FiniteTransportComplex V E F) where
  root : V
  pathTo : V → List E
  path_valid : ∀ v, K.IsEdgePathFrom root (pathTo v) v
  root_path : pathTo root = []

namespace RootedPathTree

/-- Compatibility saying that the chosen path potential changes by `sigma e`
across every edge `e`.  This is the finite path-independent core used to turn
the rooted path tree into an exact potential. -/
def IsSigmaCompatible (K : FiniteTransportComplex V E F)
    (T : RootedPathTree K) (sigma : E → ℝ) : Prop :=
  ∀ e, pathIntegral sigma (T.pathTo (K.target e)) =
    pathIntegral sigma (T.pathTo (K.source e)) + sigma e

/-- The canonical signed loop attached to one edge and a rooted path tree:
root to the source, the edge itself, then the chosen target path traversed
backwards to the root. -/
def edgeLoop (K : FiniteTransportComplex V E F)
    (T : RootedPathTree K) (e : E) : List (SignedEdgeStep E) :=
  signedForwardPath (T.pathTo (K.source e)) ++
    [signedForwardStep e] ++
      signedReversePath (T.pathTo (K.target e))

/-- All canonical rooted edge-loop periods vanish. -/
def EdgeLoopPeriodsVanish (K : FiniteTransportComplex V E F)
    (T : RootedPathTree K) (sigma : E → ℝ) : Prop :=
  ∀ e, signedPathIntegral sigma (T.edgeLoop K e) = 0

/-- Every canonical rooted edge loop bounds a finite 2-chain. -/
def EdgeLoopsBoundBy2Chains (K : FiniteTransportComplex V E F)
    (T : RootedPathTree K) : Prop :=
  ∀ e, SignedPathBoundsBy2Chain K (T.edgeLoop K e)

/-- The canonical rooted edge loop is a closed signed loop based at the root. -/
theorem edgeLoop_isClosedSignedLoop
    (K : FiniteTransportComplex V E F) (T : RootedPathTree K) (e : E) :
    IsClosedSignedLoop K T.root (T.edgeLoop K e) := by
  have hsourcePath := signedForwardPath_valid K (T.path_valid (K.source e))
  have hedge :
      IsSignedPathFrom K (K.source e) [signedForwardStep e] (K.target e) := by
    simp [IsSignedPathFrom, signedForwardStep, SignedEdgeStep.source,
      SignedEdgeStep.target]
  have htargetBack := signedReversePath_valid K (T.path_valid (K.target e))
  unfold edgeLoop IsClosedSignedLoop
  exact isSignedPathFrom_append K
    (isSignedPathFrom_append K hsourcePath hedge) htargetBack

/-- Vanishing of the canonical rooted edge-loop periods forces the path
integral compatibility condition used to construct the local potential. -/
theorem compatible_of_edgeLoopPeriodsVanish
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hvanish : T.EdgeLoopPeriodsVanish K sigma) :
    T.IsSigmaCompatible K sigma := by
  intro e
  have h := hvanish e
  unfold edgeLoop at h
  simp [signedPathIntegral_append, signedPathIntegral_forwardPath,
    signedPathIntegral_reversePath, signedPathIntegral, signedForwardStep,
    SignedEdgeStep.value] at h
  linarith

/-- Closed finite 1-cochains have vanishing periods on all canonical rooted
edge loops once those loops are certified as finite 2-chain boundaries. -/
theorem edgeLoopPeriodsVanish_of_closed_of_edgeLoopsBoundBy2Chains
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : T.EdgeLoopsBoundBy2Chains K) :
    T.EdgeLoopPeriodsVanish K sigma := by
  intro e
  exact signedPathIntegral_eq_zero_of_boundsBy2Chain_of_closed
    K sigma (T.edgeLoop K e) (hbounds e) hclosed

/-- Boundary certificates for all canonical rooted edge loops turn closedness
`dσ=0` into the rooted path-integral compatibility condition. -/
theorem compatible_of_closed_of_edgeLoopsBoundBy2Chains
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : T.EdgeLoopsBoundBy2Chains K) :
    T.IsSigmaCompatible K sigma :=
  T.compatible_of_edgeLoopPeriodsVanish K sigma
    (T.edgeLoopPeriodsVanish_of_closed_of_edgeLoopsBoundBy2Chains
      K sigma hclosed hbounds)

/-- The potential obtained by integrating `sigma` along the chosen rooted path
to each vertex. -/
def potential (K : FiniteTransportComplex V E F)
    (T : RootedPathTree K) (sigma : E → ℝ) : V → ℝ :=
  fun v => pathIntegral sigma (T.pathTo v)

/-- A compatible rooted path tree gives an exact finite 1-cochain. -/
theorem exact_of_compatible
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hcompat : RootedPathTree.IsSigmaCompatible K T sigma) :
    sigma = K.d0 (RootedPathTree.potential K T sigma) := by
  funext e
  have h := hcompat e
  simp [d0, RootedPathTree.potential]
  linarith

/-- Boundary certificates for all canonical rooted edge loops turn closedness
`dσ=0` into an exact rooted-path potential. -/
theorem exact_of_closed_of_edgeLoopsBoundBy2Chains
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : T.EdgeLoopsBoundBy2Chains K) :
    sigma = K.d0 (RootedPathTree.potential K T sigma) :=
  RootedPathTree.exact_of_compatible K sigma T
    (RootedPathTree.compatible_of_closed_of_edgeLoopsBoundBy2Chains
      K sigma T hclosed hbounds)

end RootedPathTree

/-- Certificate that a finite local 1-cochain is exact, carried by an explicit
potential.  This is the finite algebraic core behind local exactness statements;
existence of such a certificate from contractibility is a separate topological
input. -/
structure LocalExactPotential (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) where
  potential : V → ℝ
  exact : sigma = K.d0 potential

namespace LocalExactPotential

/-- Link phase factorization induced by an explicit finite local potential. -/
theorem phase_factorization
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (P : K.LocalExactPotential sigma) (Lambda : ℝ) (e : E) :
    phase Lambda (sigma e) =
      phase Lambda (-(P.potential (K.source e))) *
        phase Lambda (P.potential (K.target e)) := by
  have hendpoint := endpointPhaseAction K Lambda (fun _ : E => 0) P.potential e
  have hd0 : K.d0 P.potential e = sigma e := (congrFun P.exact e).symm
  have hexact :
      K.exactShift (fun _ : E => 0) P.potential e = sigma e := by
    simp [exactShift, hd0]
  rw [← hexact]
  rw [hendpoint]
  simp [phase_zero]

/-- Closed-chain holonomy of an exact finite local potential is trivial. -/
theorem closedChainHolonomy_eq_one
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (P : K.LocalExactPotential sigma) (Lambda : ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda sigma c = 1 := by
  unfold chainHolonomy
  rw [P.exact]
  rw [hclosed P.potential]
  exact phase_zero Lambda

end LocalExactPotential

/-- Finite local exactness certificate: a rooted path tree together with
2-chain boundary certificates for all canonical rooted edge loops.  This is the
combinatorial data needed to derive local exactness from `dσ=0`; the separate
topological statement is that contractible finite patches provide such data. -/
structure LocalExactnessCertificate (K : FiniteTransportComplex V E F) where
  tree : RootedPathTree K
  edgeLoop_boundaries : RootedPathTree.EdgeLoopsBoundBy2Chains K tree

namespace LocalExactnessCertificate

/-- Potential associated with a finite local exactness certificate. -/
def potential (K : FiniteTransportComplex V E F)
    (C : LocalExactnessCertificate K) (sigma : E → ℝ) : V → ℝ :=
  RootedPathTree.potential K C.tree sigma

/-- Closedness `dσ=0` and the certificate imply rooted path-tree
compatibility. -/
theorem compatible_of_closed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma) :
    RootedPathTree.IsSigmaCompatible K C.tree sigma :=
  RootedPathTree.compatible_of_closed_of_edgeLoopsBoundBy2Chains
    K sigma C.tree hclosed C.edgeLoop_boundaries

/-- Closedness `dσ=0` and the certificate imply exactness of the constructed
finite potential. -/
theorem exact_of_closed
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma) :
    sigma = K.d0 (C.potential K sigma) :=
  RootedPathTree.exact_of_closed_of_edgeLoopsBoundBy2Chains
    K sigma C.tree hclosed C.edgeLoop_boundaries

/-- The certificate packaged as an explicit local exact-potential certificate
for a closed finite 1-cochain. -/
def localExactPotential
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma) :
    K.LocalExactPotential sigma where
  potential := C.potential K sigma
  exact := C.exact_of_closed K sigma hclosed

end LocalExactnessCertificate

/-- The compatible rooted path tree packaged as a local exact-potential
certificate. -/
def RootedPathTree.localExactPotential
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hcompat : RootedPathTree.IsSigmaCompatible K T sigma) :
    K.LocalExactPotential sigma where
  potential := RootedPathTree.potential K T sigma
  exact := RootedPathTree.exact_of_compatible K sigma T hcompat

/-- Paper-facing exactness of the potential constructed by integrating along a
compatible rooted finite path tree. -/
theorem finiteRootedPathTreePotentialExact
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hcompat : RootedPathTree.IsSigmaCompatible K T sigma) :
    sigma = K.d0 (RootedPathTree.potential K T sigma) :=
  RootedPathTree.exact_of_compatible K sigma T hcompat

/-- Paper-facing finite step from vanishing rooted edge-loop periods to rooted
path-tree compatibility. -/
theorem finiteRootedPathTreeCompatibleOfEdgeLoopPeriodsVanish
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hvanish : RootedPathTree.EdgeLoopPeriodsVanish K T sigma) :
    RootedPathTree.IsSigmaCompatible K T sigma :=
  RootedPathTree.compatible_of_edgeLoopPeriodsVanish K sigma T hvanish

/-- Paper-facing exactness of the rooted-path potential when all canonical
rooted edge-loop periods vanish. -/
theorem finiteRootedPathTreePotentialExactOfEdgeLoopPeriodsVanish
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hvanish : RootedPathTree.EdgeLoopPeriodsVanish K T sigma) :
    sigma = K.d0 (RootedPathTree.potential K T sigma) :=
  RootedPathTree.exact_of_compatible K sigma T
    (RootedPathTree.compatible_of_edgeLoopPeriodsVanish K sigma T hvanish)

/-- Paper-facing Stokes consequence for a signed finite path certified as a
2-chain boundary. -/
theorem finiteSignedPathIntegralEqZeroOfBoundaryCertificate
    (K : FiniteTransportComplex V E F)
    (sigma : E → ℝ) (steps : List (SignedEdgeStep E))
    (hbounds : SignedPathBoundsBy2Chain K steps)
    (hclosed : K.IsClosed1Cochain sigma) :
    signedPathIntegral sigma steps = 0 :=
  signedPathIntegral_eq_zero_of_boundsBy2Chain_of_closed
    K sigma steps hbounds hclosed

/-- Paper-facing Stokes consequence for all canonical rooted edge loops. -/
theorem finiteRootedPathTreeEdgeLoopPeriodsVanishOfClosedAndBoundaryCertificates
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : RootedPathTree.EdgeLoopsBoundBy2Chains K T) :
    RootedPathTree.EdgeLoopPeriodsVanish K T sigma :=
  RootedPathTree.edgeLoopPeriodsVanish_of_closed_of_edgeLoopsBoundBy2Chains
    K sigma T hclosed hbounds

/-- Paper-facing compatibility consequence of closedness plus finite 2-chain
boundary certificates for all canonical rooted edge loops. -/
theorem finiteRootedPathTreeCompatibleOfClosedAndBoundaryCertificates
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : RootedPathTree.EdgeLoopsBoundBy2Chains K T) :
    RootedPathTree.IsSigmaCompatible K T sigma :=
  RootedPathTree.compatible_of_closed_of_edgeLoopsBoundBy2Chains
    K sigma T hclosed hbounds

/-- Paper-facing exact rooted-path potential from closedness plus finite 2-chain
boundary certificates for all canonical rooted edge loops. -/
theorem finiteRootedPathTreePotentialExactOfClosedAndBoundaryCertificates
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hclosed : K.IsClosed1Cochain sigma)
    (hbounds : RootedPathTree.EdgeLoopsBoundBy2Chains K T) :
    sigma = K.d0 (RootedPathTree.potential K T sigma) :=
  RootedPathTree.exact_of_closed_of_edgeLoopsBoundBy2Chains
    K sigma T hclosed hbounds

/-- Paper-facing exact potential from a finite local exactness certificate and
closedness `dσ=0`. -/
theorem finiteLocalExactnessCertificatePotentialExact
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma) :
    sigma = K.d0 (LocalExactnessCertificate.potential K C sigma) :=
  C.exact_of_closed K sigma hclosed

/-- Paper-facing construction of an explicit local exact-potential certificate
from a finite local exactness certificate and closedness `dσ=0`. -/
def finiteLocalExactnessCertificateLocalExactPotential
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma) :
    K.LocalExactPotential sigma :=
  C.localExactPotential K sigma hclosed

/-- Paper-facing phase factorization from a finite local exactness certificate
and closedness `dσ=0`. -/
theorem finiteLocalExactnessCertificatePhaseFactorization
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosed : K.IsClosed1Cochain sigma)
    (Lambda : ℝ) (e : E) :
    phase Lambda (sigma e) =
      phase Lambda (-(LocalExactnessCertificate.potential K C sigma (K.source e))) *
        phase Lambda (LocalExactnessCertificate.potential K C sigma (K.target e)) :=
  (C.localExactPotential K sigma hclosed).phase_factorization K sigma Lambda e

/-- Paper-facing closed-chain holonomy triviality from a finite local exactness
certificate and closedness `dσ=0`. -/
theorem finiteLocalExactnessCertificateClosedChainHolonomyEqOne
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (C : LocalExactnessCertificate K)
    (hclosedCochain : K.IsClosed1Cochain sigma)
    (Lambda : ℝ) (c : E → ℤ) (hclosedChain : K.IsClosed1Chain c) :
    chainHolonomy Lambda sigma c = 1 :=
  (C.localExactPotential K sigma hclosedCochain).closedChainHolonomy_eq_one
    K sigma Lambda c hclosedChain

/-- Paper-facing phase factorization induced by a compatible rooted finite path
tree. -/
theorem finiteRootedPathTreePhaseFactorization
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hcompat : RootedPathTree.IsSigmaCompatible K T sigma)
    (Lambda : ℝ) (e : E) :
    phase Lambda (sigma e) =
      phase Lambda (-(RootedPathTree.potential K T sigma (K.source e))) *
        phase Lambda (RootedPathTree.potential K T sigma (K.target e)) :=
  (RootedPathTree.localExactPotential K sigma T hcompat).phase_factorization
    K sigma Lambda e

/-- Paper-facing closed-chain holonomy triviality induced by a compatible rooted
finite path tree. -/
theorem finiteRootedPathTreeClosedChainHolonomyEqOne
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (T : RootedPathTree K)
    (hcompat : RootedPathTree.IsSigmaCompatible K T sigma)
    (Lambda : ℝ) (c : E → ℤ) (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda sigma c = 1 :=
  (RootedPathTree.localExactPotential K sigma T hcompat).closedChainHolonomy_eq_one
    K sigma Lambda c hclosed

/-- Paper-facing finite local exact-potential phase factorization. -/
theorem finiteLocalExactPotentialPhaseFactorization
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (P : K.LocalExactPotential sigma) (Lambda : ℝ) (e : E) :
    phase Lambda (sigma e) =
      phase Lambda (-(P.potential (K.source e))) *
        phase Lambda (P.potential (K.target e)) :=
  P.phase_factorization K sigma Lambda e

/-- Paper-facing finite local exact-potential closed-chain triviality. -/
theorem finiteLocalExactPotentialClosedChainHolonomyEqOne
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ)
    (P : K.LocalExactPotential sigma) (Lambda : ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda sigma c = 1 :=
  P.closedChainHolonomy_eq_one K sigma Lambda c hclosed

/-! ### Reduced holonomy Noether core -/

section ReducedHolonomyNoether

variable {H Y : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Reduced holonomy charge for an orthogonal finite-dimensional reduced
sector.  This is the Lean form of `Q(x)=<x,(I-h)x>`. -/
noncomputable def reducedHolonomyCharge (h : H ≃ₗᵢ[ℝ] H) (x : H) : ℝ :=
  inner ℝ x (x - h x)

/-- The reduced holonomy charge is invariant under one forward holonomy step. -/
theorem reducedHolonomyCharge_apply (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    reducedHolonomyCharge h (h x) = reducedHolonomyCharge h x := by
  unfold reducedHolonomyCharge
  rw [← h.inner_map_map x (x - h x)]
  congr 1
  rw [map_sub]

/-- The reduced holonomy charge is invariant under one backward holonomy step. -/
theorem reducedHolonomyCharge_symm_apply (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    reducedHolonomyCharge h (h.symm x) = reducedHolonomyCharge h x := by
  simpa using (reducedHolonomyCharge_apply h (h.symm x)).symm

/-- The reduced holonomy charge is unchanged along every forward discrete
holonomy orbit. -/
theorem reducedHolonomyCharge_iterate (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    ∀ n : ℕ, reducedHolonomyCharge h ((h : H → H)^[n] x) =
      reducedHolonomyCharge h x
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply']
      rw [reducedHolonomyCharge_apply]
      exact reducedHolonomyCharge_iterate h x n

/-- Application form for a positive power of an orthogonal holonomy. -/
theorem reducedHolonomyPower_succ_apply (h : H ≃ₗᵢ[ℝ] H) (x : H) (n : ℕ) :
    (h ^ (n + 1) : H ≃ₗᵢ[ℝ] H) x =
      h ((h ^ n : H ≃ₗᵢ[ℝ] H) x) := by
  rw [show (h ^ (n + 1) : H ≃ₗᵢ[ℝ] H) x =
    (h ^ n : H ≃ₗᵢ[ℝ] H) (h x) by simp [pow_succ]]
  have hcomm : (h ^ n : H ≃ₗᵢ[ℝ] H) * h =
      h * (h ^ n : H ≃ₗᵢ[ℝ] H) := by
    group
  exact congrFun (congrArg DFunLike.coe hcomm) x

/-- Application form for a positive power of the inverse holonomy. -/
theorem reducedHolonomyInvPower_succ_apply (h : H ≃ₗᵢ[ℝ] H) (x : H) (n : ℕ) :
    ((h⁻¹) ^ (n + 1) : H ≃ₗᵢ[ℝ] H) x =
      h.symm (((h⁻¹) ^ n : H ≃ₗᵢ[ℝ] H) x) := by
  rw [show ((h⁻¹) ^ (n + 1) : H ≃ₗᵢ[ℝ] H) x =
    ((h⁻¹) ^ n : H ≃ₗᵢ[ℝ] H) (h.symm x) by simp [pow_succ]]
  have hcomm : ((h⁻¹) ^ n : H ≃ₗᵢ[ℝ] H) * h⁻¹ =
      h⁻¹ * ((h⁻¹) ^ n : H ≃ₗᵢ[ℝ] H) := by
    group
  exact congrFun (congrArg DFunLike.coe hcomm) x

/-- The reduced holonomy charge is unchanged under every nonnegative group
power. -/
theorem reducedHolonomyCharge_natPower (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    ∀ n : ℕ,
      reducedHolonomyCharge h ((h ^ n : H ≃ₗᵢ[ℝ] H) x) =
        reducedHolonomyCharge h x
  | 0 => by simp
  | n + 1 => by
      rw [reducedHolonomyPower_succ_apply]
      rw [reducedHolonomyCharge_apply]
      exact reducedHolonomyCharge_natPower h x n

/-- The reduced holonomy charge is unchanged under every nonnegative inverse
group power. -/
theorem reducedHolonomyCharge_invNatPower (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    ∀ n : ℕ,
      reducedHolonomyCharge h (((h⁻¹) ^ n : H ≃ₗᵢ[ℝ] H) x) =
        reducedHolonomyCharge h x
  | 0 => by simp
  | n + 1 => by
      rw [reducedHolonomyInvPower_succ_apply]
      rw [reducedHolonomyCharge_symm_apply]
      exact reducedHolonomyCharge_invNatPower h x n

/-- The reduced holonomy charge is unchanged along every integer holonomy
orbit. -/
theorem reducedHolonomyCharge_zpow (h : H ≃ₗᵢ[ℝ] H) (x : H) (k : ℤ) :
    reducedHolonomyCharge h ((h ^ k : H ≃ₗᵢ[ℝ] H) x) =
      reducedHolonomyCharge h x := by
  cases k using Int.rec with
  | ofNat n =>
      change reducedHolonomyCharge h ((h ^ (n : ℤ) : H ≃ₗᵢ[ℝ] H) x) =
        reducedHolonomyCharge h x
      rw [zpow_natCast]
      exact reducedHolonomyCharge_natPower h x n
  | negSucc n =>
      rw [zpow_negSucc]
      have hpow : ((h ^ (n + 1))⁻¹ : H ≃ₗᵢ[ℝ] H) =
          ((h⁻¹) ^ (n + 1) : H ≃ₗᵢ[ℝ] H) := by
        exact (inv_pow h (n + 1)).symm
      rw [hpow]
      exact reducedHolonomyCharge_invNatPower h x (n + 1)

/-- For an orthogonal holonomy, the reduced charge is half the squared step
length. -/
theorem reducedHolonomyCharge_eq_half_norm_sq (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    reducedHolonomyCharge h x = (1 / 2 : ℝ) * ‖x - h x‖ ^ 2 := by
  unfold reducedHolonomyCharge
  rw [← real_inner_self_eq_norm_sq (x - h x)]
  rw [inner_sub_left, inner_sub_right, inner_sub_right]
  rw [h.inner_map_map]
  rw [real_inner_comm (h x) x]
  ring

/-- Positivity of the reduced holonomy charge. -/
theorem reducedHolonomyCharge_nonneg (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    0 ≤ reducedHolonomyCharge h x := by
  rw [reducedHolonomyCharge_eq_half_norm_sq]
  positivity

/-- The reduced holonomy charge vanishes exactly at one-step fixed points. -/
theorem reducedHolonomyCharge_eq_zero_iff_fixed (h : H ≃ₗᵢ[ℝ] H) (x : H) :
    reducedHolonomyCharge h x = 0 ↔ h x = x := by
  rw [reducedHolonomyCharge_eq_half_norm_sq]
  constructor
  · intro hzero
    have hsq : ‖x - h x‖ ^ 2 = 0 := by
      nlinarith [sq_nonneg ‖x - h x‖]
    have hnorm : ‖x - h x‖ = 0 := sq_eq_zero_iff.mp hsq
    have hstep : x - h x = 0 := norm_eq_zero.mp hnorm
    exact (sub_eq_zero.mp hstep).symm
  · intro hfixed
    rw [hfixed, sub_self, norm_zero]
    norm_num

/-- If a holonomy has period `p`, then every forward orbit closes after `p`
steps. -/
theorem reducedHolonomyOrbit_periodic (h : H ≃ₗᵢ[ℝ] H) (p : ℕ)
    (hperiod : (h : H → H)^[p] = id) (x : H) (n : ℕ) :
    (h : H → H)^[n + p] x = (h : H → H)^[n] x := by
  rw [Function.iterate_add]
  simp [hperiod]

/-- Integer-period form: if `h^p=1`, then integer holonomy orbits close after
`p`. -/
theorem reducedHolonomyOrbit_zperiodic (h : H ≃ₗᵢ[ℝ] H) (p k : ℤ)
    (hperiod : h ^ p = 1) (x : H) :
    ((h ^ (k + p) : H ≃ₗᵢ[ℝ] H) x) = ((h ^ k : H ≃ₗᵢ[ℝ] H) x) := by
  rw [zpow_add, hperiod]
  simp

/-- Object-level reduced sigma-holonomy datum: a real inner-product sector together
with an orthogonal holonomy operator.  This packages the finite Noether object
used in the paper without adding dynamics. -/
structure ReducedHolonomyData (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℝ H] where
  hol : H ≃ₗᵢ[ℝ] H

namespace ReducedHolonomyData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- Reduced charge attached to a reduced holonomy datum. -/
noncomputable def charge (X : ReducedHolonomyData H) (x : H) : ℝ :=
  reducedHolonomyCharge X.hol x

/-- Forward natural-number orbit of a reduced holonomy datum. -/
def orbitNat (X : ReducedHolonomyData H) (x : H) (n : ℕ) : H :=
  ((X.hol : H → H)^[n]) x

/-- Integer orbit of a reduced holonomy datum. -/
def orbitInt (X : ReducedHolonomyData H) (x : H) (k : ℤ) : H :=
  (X.hol ^ k : H ≃ₗᵢ[ℝ] H) x

/-- Object-level one-step conservation of the reduced holonomy charge. -/
theorem charge_hol (X : ReducedHolonomyData H) (x : H) :
    X.charge (X.hol x) = X.charge x :=
  reducedHolonomyCharge_apply X.hol x

/-- Object-level conservation along every forward reduced holonomy orbit. -/
theorem charge_orbitNat (X : ReducedHolonomyData H) (x : H) (n : ℕ) :
    X.charge (X.orbitNat x n) = X.charge x :=
  reducedHolonomyCharge_iterate X.hol x n

/-- Object-level conservation along every integer reduced holonomy orbit. -/
theorem charge_orbitInt (X : ReducedHolonomyData H) (x : H) (k : ℤ) :
    X.charge (X.orbitInt x k) = X.charge x :=
  reducedHolonomyCharge_zpow X.hol x k

/-- Object-level half squared step-length form of the reduced charge. -/
theorem charge_eq_half_norm_sq (X : ReducedHolonomyData H) (x : H) :
    X.charge x = (1 / 2 : ℝ) * ‖x - X.hol x‖ ^ 2 :=
  reducedHolonomyCharge_eq_half_norm_sq X.hol x

/-- Object-level positivity of the reduced holonomy charge. -/
theorem charge_nonneg (X : ReducedHolonomyData H) (x : H) :
    0 ≤ X.charge x :=
  reducedHolonomyCharge_nonneg X.hol x

/-- Object-level zero-charge criterion: zero charge is equivalent to a
one-step holonomy fixed point. -/
theorem charge_eq_zero_iff_fixed (X : ReducedHolonomyData H) (x : H) :
    X.charge x = 0 ↔ X.hol x = x :=
  reducedHolonomyCharge_eq_zero_iff_fixed X.hol x

/-- Zero reduced holonomy charge makes the whole forward orbit stationary. -/
theorem orbitNat_eq_self_of_charge_eq_zero (X : ReducedHolonomyData H) (x : H)
    (hzero : X.charge x = 0) (n : ℕ) :
    X.orbitNat x n = x := by
  have hfixed : X.hol x = x := (X.charge_eq_zero_iff_fixed x).mp hzero
  change ((X.hol : H → H)^[n]) x = x
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      rw [ih]
      exact hfixed

/-- A natural-number period closes every forward reduced holonomy orbit. -/
theorem orbitNat_periodic (X : ReducedHolonomyData H) (p : ℕ)
    (hperiod : (X.hol : H → H)^[p] = id) (x : H) (n : ℕ) :
    X.orbitNat x (n + p) = X.orbitNat x n :=
  reducedHolonomyOrbit_periodic X.hol p hperiod x n

/-- An integer group period closes every integer reduced holonomy orbit. -/
theorem orbitInt_periodic (X : ReducedHolonomyData H) (p k : ℤ)
    (hperiod : X.hol ^ p = 1) (x : H) :
    X.orbitInt x (k + p) = X.orbitInt x k :=
  reducedHolonomyOrbit_zperiodic X.hol p k hperiod x

end ReducedHolonomyData

/-- Cyclic reduced sigma-holonomy datum: the reduced holonomy object together
with a positive finite period. -/
structure CyclicReducedHolonomyData (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℝ H] extends ReducedHolonomyData H where
  period : ℕ
  period_pos : 0 < period
  period_closed : (toReducedHolonomyData.hol : H → H)^[period] = id

namespace CyclicReducedHolonomyData

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The stored period closes every forward orbit of a cyclic reduced holonomy
datum. -/
theorem orbitNat_periodic (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.orbitNat x (n + X.period) =
      X.toReducedHolonomyData.orbitNat x n :=
  ReducedHolonomyData.orbitNat_periodic X.toReducedHolonomyData X.period
    X.period_closed x n

/-- The reduced charge is conserved along every forward orbit of a cyclic
reduced holonomy datum. -/
theorem charge_orbitNat (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.charge
      (X.toReducedHolonomyData.orbitNat x n) =
        X.toReducedHolonomyData.charge x :=
  ReducedHolonomyData.charge_orbitNat X.toReducedHolonomyData x n

end CyclicReducedHolonomyData

/-- Paper-facing object-level reduced holonomy conservation for all integer
orbit times. -/
theorem finiteReducedHolonomyDataChargeIntegerOrbitInvariant
    (X : ReducedHolonomyData H) (x : H) (k : ℤ) :
    X.charge (X.orbitInt x k) = X.charge x :=
  ReducedHolonomyData.charge_orbitInt X x k

/-- Paper-facing object-level half squared step-length identity for the reduced
holonomy charge. -/
theorem finiteReducedHolonomyDataChargeHalfNormSq
    (X : ReducedHolonomyData H) (x : H) :
    X.charge x = (1 / 2 : ℝ) * ‖x - X.hol x‖ ^ 2 :=
  ReducedHolonomyData.charge_eq_half_norm_sq X x

/-- Paper-facing object-level nonnegativity of the reduced holonomy charge. -/
theorem finiteReducedHolonomyDataChargeNonnegative
    (X : ReducedHolonomyData H) (x : H) :
    0 ≤ X.charge x :=
  ReducedHolonomyData.charge_nonneg X x

/-- Paper-facing zero-charge criterion for reduced holonomy data. -/
theorem finiteReducedHolonomyDataChargeZeroIffFixed
    (X : ReducedHolonomyData H) (x : H) :
    X.charge x = 0 ↔ X.hol x = x :=
  ReducedHolonomyData.charge_eq_zero_iff_fixed X x

/-- Paper-facing stationarity of the whole forward orbit at zero reduced
holonomy charge. -/
theorem finiteReducedHolonomyDataZeroChargeOrbitConstant
    (X : ReducedHolonomyData H) (x : H) (hzero : X.charge x = 0) (n : ℕ) :
    X.orbitNat x n = x :=
  ReducedHolonomyData.orbitNat_eq_self_of_charge_eq_zero X x hzero n

/-- Paper-facing closure of the forward orbit of a cyclic reduced holonomy datum. -/
theorem finiteCyclicReducedHolonomyDataOrbitClosed
    (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.orbitNat x (n + X.period) =
      X.toReducedHolonomyData.orbitNat x n :=
  CyclicReducedHolonomyData.orbitNat_periodic X x n

/-- Paper-facing conservation of the reduced charge along a cyclic reduced
holonomy orbit. -/
theorem finiteCyclicReducedHolonomyDataChargeInvariant
    (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.charge
      (X.toReducedHolonomyData.orbitNat x n) =
        X.toReducedHolonomyData.charge x :=
  CyclicReducedHolonomyData.charge_orbitNat X x n

/-- Paper-facing zero-charge criterion for cyclic reduced holonomy data. -/
theorem finiteCyclicReducedHolonomyDataChargeZeroIffFixed
    (X : CyclicReducedHolonomyData H) (x : H) :
    X.toReducedHolonomyData.charge x = 0 ↔
      X.toReducedHolonomyData.hol x = x :=
  ReducedHolonomyData.charge_eq_zero_iff_fixed X.toReducedHolonomyData x

/-- Paper-facing stationarity of a cyclic reduced holonomy orbit at zero
charge. -/
theorem finiteCyclicReducedHolonomyDataZeroChargeOrbitConstant
    (X : CyclicReducedHolonomyData H) (x : H)
    (hzero : X.toReducedHolonomyData.charge x = 0) (n : ℕ) :
    X.toReducedHolonomyData.orbitNat x n = x :=
  ReducedHolonomyData.orbitNat_eq_self_of_charge_eq_zero
    X.toReducedHolonomyData x hzero n

/-- A morphism of reduced holonomy data is an isometric linear map that
intertwines the two orthogonal holonomy operators. -/
structure ReducedHolonomyMorphism (hX : H ≃ₗᵢ[ℝ] H) (hY : Y ≃ₗᵢ[ℝ] Y) where
  map : H →ₗᵢ[ℝ] Y
  intertwines : ∀ x : H, map (hX x) = hY (map x)

namespace ReducedHolonomyMorphism

/-- Intertwining propagates along all forward iterates. -/
theorem map_comm_iterate {hX : H ≃ₗᵢ[ℝ] H} {hY : Y ≃ₗᵢ[ℝ] Y}
    (f : ReducedHolonomyMorphism hX hY) :
    ∀ (n : ℕ) (x : H),
      f.map (((hX : H → H)^[n]) x) = ((hY : Y → Y)^[n]) (f.map x)
  | 0, x => rfl
  | n + 1, x => by
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      rw [f.intertwines]
      exact congrArg hY (f.map_comm_iterate n x)

/-- Reduced holonomy charge is functorial under isometric intertwiners. -/
theorem charge_preserving {hX : H ≃ₗᵢ[ℝ] H} {hY : Y ≃ₗᵢ[ℝ] Y}
    (f : ReducedHolonomyMorphism hX hY) (x : H) :
    reducedHolonomyCharge hY (f.map x) = reducedHolonomyCharge hX x := by
  unfold reducedHolonomyCharge
  rw [← f.map.inner_map_map x (x - hX x)]
  congr 1
  rw [map_sub]
  rw [f.intertwines]

/-- Functoriality also holds pointwise along corresponding reduced holonomy
orbits. -/
theorem orbit_charge_preserving {hX : H ≃ₗᵢ[ℝ] H} {hY : Y ≃ₗᵢ[ℝ] Y}
    (f : ReducedHolonomyMorphism hX hY) (x : H) (n : ℕ) :
    reducedHolonomyCharge hY (((hY : Y → Y)^[n]) (f.map x)) =
      reducedHolonomyCharge hX (((hX : H → H)^[n]) x) := by
  rw [← f.map_comm_iterate n x]
  exact f.charge_preserving (((hX : H → H)^[n]) x)

end ReducedHolonomyMorphism

/-- Object-level morphism of reduced holonomy data.  It is an isometric linear
map that intertwines the stored orthogonal holonomy operators. -/
structure ReducedHolonomyDataMorphism
    (X : ReducedHolonomyData H) (Ydata : ReducedHolonomyData Y) where
  map : H →ₗᵢ[ℝ] Y
  intertwines : ∀ x : H, map (X.hol x) = Ydata.hol (map x)

namespace ReducedHolonomyDataMorphism

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- Identity morphism of a reduced holonomy datum. -/
def identity (X : ReducedHolonomyData H) : ReducedHolonomyDataMorphism X X where
  map := LinearIsometry.id
  intertwines := fun _ => rfl

/-- Composition of reduced holonomy datum morphisms. -/
def comp {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) :
    ReducedHolonomyDataMorphism X Zdata where
  map := g.map.comp f.map
  intertwines := by
    intro x
    change g.map (f.map (X.hol x)) = Zdata.hol (g.map (f.map x))
    rw [f.intertwines x]
    exact g.intertwines (f.map x)

/-- Identity morphisms act as the identity on points. -/
theorem identity_map (X : ReducedHolonomyData H) (x : H) :
    (identity X).map x = x :=
  rfl

/-- Composition of reduced holonomy datum morphisms acts by function
composition on points. -/
theorem comp_map {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp g f).map x = g.map (f.map x) :=
  rfl

/-- Left identity law, stated pointwise on the underlying map. -/
theorem identity_comp_map {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp (identity Ydata) f).map x = f.map x :=
  rfl

/-- Right identity law, stated pointwise on the underlying map. -/
theorem comp_identity_map {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp f (identity X)).map x = f.map x :=
  rfl

/-- Associativity of composition, stated pointwise on the underlying map. -/
theorem comp_assoc_map
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {Wdata : ReducedHolonomyData W}
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (h : ReducedHolonomyDataMorphism Zdata Wdata)
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp h (comp g f)).map x = (comp (comp h g) f).map x :=
  rfl

/-- The identity morphism preserves the reduced holonomy charge. -/
theorem identity_charge_preserving (X : ReducedHolonomyData H) (x : H) :
    X.charge ((identity X).map x) = X.charge x :=
  rfl

/-- Composition of reduced holonomy datum morphisms preserves the reduced
holonomy charge. -/
theorem comp_charge_preserving {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    Zdata.charge ((comp g f).map x) = X.charge x := by
  rw [comp_map g f x]
  let gop : ReducedHolonomyMorphism Ydata.hol Zdata.hol :=
    { map := g.map, intertwines := g.intertwines }
  let fop : ReducedHolonomyMorphism X.hol Ydata.hol :=
    { map := f.map, intertwines := f.intertwines }
  exact (gop.charge_preserving (f.map x)).trans (fop.charge_preserving x)

/-- Composition of reduced holonomy datum morphisms intertwines forward
orbits. -/
theorem comp_orbit_intertwining {X : ReducedHolonomyData H}
    {Ydata : ReducedHolonomyData Y} {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    (comp g f).map (X.orbitNat x n) =
      Zdata.orbitNat ((comp g f).map x) n := by
  let op : ReducedHolonomyMorphism X.hol Zdata.hol :=
    { map := (comp g f).map, intertwines := (comp g f).intertwines }
  exact op.map_comm_iterate n x

/-- Forgetting the object wrappers gives the operator-level morphism. -/
def toOperatorMorphism {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) :
    ReducedHolonomyMorphism X.hol Ydata.hol where
  map := f.map
  intertwines := f.intertwines

/-- Object-level orbit intertwining for forward iterates. -/
theorem map_comm_orbitNat {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    f.map (X.orbitNat x n) = Ydata.orbitNat (f.map x) n :=
  f.toOperatorMorphism.map_comm_iterate n x

/-- Object-level functoriality of the reduced holonomy charge. -/
theorem charge_preserving {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.charge (f.map x) = X.charge x :=
  f.toOperatorMorphism.charge_preserving x

/-- The Noether step length is preserved by an object-level reduced holonomy
morphism. -/
theorem step_norm_preserving {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    ‖f.map x - Ydata.hol (f.map x)‖ = ‖x - X.hol x‖ := by
  rw [← f.intertwines x]
  rw [← map_sub]
  exact f.map.norm_map (x - X.hol x)

/-- Object-level functoriality of the reduced charge along corresponding
forward orbits. -/
theorem orbit_charge_preserving {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.charge (Ydata.orbitNat (f.map x) n) =
      X.charge (X.orbitNat x n) := by
  rw [← f.map_comm_orbitNat x n]
  exact f.charge_preserving (X.orbitNat x n)

/-- Object-level conservation of the reduced charge after mapping a forward
orbit by a reduced holonomy morphism. -/
theorem mapped_orbit_charge_constant
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.charge (Ydata.orbitNat (f.map x) n) = X.charge x := by
  rw [f.orbit_charge_preserving x n]
  exact ReducedHolonomyData.charge_orbitNat X x n

end ReducedHolonomyDataMorphism

/-- Paper-facing morphism functoriality of reduced holonomy charge. -/
theorem finiteReducedHolonomyDataMorphismChargePreserving
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.charge (f.map x) = X.charge x :=
  ReducedHolonomyDataMorphism.charge_preserving f x

/-- Paper-facing morphism intertwining of forward reduced holonomy orbits. -/
theorem finiteReducedHolonomyDataMorphismOrbitIntertwining
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    f.map (X.orbitNat x n) = Ydata.orbitNat (f.map x) n :=
  ReducedHolonomyDataMorphism.map_comm_orbitNat f x n

/-- Paper-facing preservation of the Noether step norm by a reduced holonomy
morphism. -/
theorem finiteReducedHolonomyDataMorphismStepNormPreserving
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    ‖f.map x - Ydata.hol (f.map x)‖ = ‖x - X.hol x‖ :=
  ReducedHolonomyDataMorphism.step_norm_preserving f x

/-- Paper-facing charge preservation along corresponding forward reduced
holonomy orbits. -/
theorem finiteReducedHolonomyDataMorphismOrbitChargePreserving
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.charge (Ydata.orbitNat (f.map x) n) =
      X.charge (X.orbitNat x n) :=
  ReducedHolonomyDataMorphism.orbit_charge_preserving f x n

/-- Paper-facing mapped-orbit conservation law for reduced holonomy morphisms. -/
theorem finiteReducedHolonomyDataMorphismMappedOrbitChargeConstant
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.charge (Ydata.orbitNat (f.map x) n) = X.charge x :=
  ReducedHolonomyDataMorphism.mapped_orbit_charge_constant f x n

/-- Paper-facing identity morphism on a reduced holonomy datum. -/
def finiteReducedHolonomyDataIdentityMorphism
    (X : ReducedHolonomyData H) : ReducedHolonomyDataMorphism X X :=
  ReducedHolonomyDataMorphism.identity X

/-- Paper-facing pointwise action of the identity morphism. -/
theorem finiteReducedHolonomyDataIdentityMorphismMap
    (X : ReducedHolonomyData H) (x : H) :
    (finiteReducedHolonomyDataIdentityMorphism X).map x = x :=
  ReducedHolonomyDataMorphism.identity_map X x

/-- Paper-facing composition of reduced holonomy datum morphisms. -/
def finiteReducedHolonomyDataMorphismComp
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) :
    ReducedHolonomyDataMorphism X Zdata :=
  ReducedHolonomyDataMorphism.comp g f

/-- Paper-facing pointwise action of a composed reduced holonomy datum
morphism. -/
theorem finiteReducedHolonomyDataMorphismCompMap
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (finiteReducedHolonomyDataMorphismComp g f).map x = g.map (f.map x) :=
  ReducedHolonomyDataMorphism.comp_map g f x

/-- Paper-facing charge preservation under a composed reduced holonomy datum
morphism. -/
theorem finiteReducedHolonomyDataMorphismCompChargePreserving
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    Zdata.charge ((finiteReducedHolonomyDataMorphismComp g f).map x) =
      X.charge x :=
  ReducedHolonomyDataMorphism.comp_charge_preserving g f x

/-- Paper-facing orbit intertwining under a composed reduced holonomy datum
morphism. -/
theorem finiteReducedHolonomyDataMorphismCompOrbitIntertwining
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    (finiteReducedHolonomyDataMorphismComp g f).map (X.orbitNat x n) =
      Zdata.orbitNat ((finiteReducedHolonomyDataMorphismComp g f).map x) n :=
  ReducedHolonomyDataMorphism.comp_orbit_intertwining g f x n

/-- Paper-facing left identity law for reduced holonomy datum morphisms. -/
theorem finiteReducedHolonomyDataMorphismLeftIdentityMap
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (ReducedHolonomyDataMorphism.comp
      (ReducedHolonomyDataMorphism.identity Ydata) f).map x = f.map x :=
  ReducedHolonomyDataMorphism.identity_comp_map f x

/-- Paper-facing right identity law for reduced holonomy datum morphisms. -/
theorem finiteReducedHolonomyDataMorphismRightIdentityMap
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (ReducedHolonomyDataMorphism.comp f
      (ReducedHolonomyDataMorphism.identity X)).map x = f.map x :=
  ReducedHolonomyDataMorphism.comp_identity_map f x

/-- Paper-facing associativity law for reduced holonomy datum morphism
composition. -/
theorem finiteReducedHolonomyDataMorphismAssocMap
    {Z W : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {Wdata : ReducedHolonomyData W}
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (h : ReducedHolonomyDataMorphism Zdata Wdata)
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (ReducedHolonomyDataMorphism.comp h
      (ReducedHolonomyDataMorphism.comp g f)).map x =
        (ReducedHolonomyDataMorphism.comp
          (ReducedHolonomyDataMorphism.comp h g) f).map x :=
  ReducedHolonomyDataMorphism.comp_assoc_map h g f x

/-- Morphism between cyclic reduced holonomy data.  The morphism is the same
isometric intertwiner as for reduced holonomy data, now with cyclic source and
target objects retained. -/
structure CyclicReducedHolonomyDataMorphism
    (X : CyclicReducedHolonomyData H) (Ydata : CyclicReducedHolonomyData Y) where
  toReducedMorphism :
    ReducedHolonomyDataMorphism X.toReducedHolonomyData Ydata.toReducedHolonomyData

namespace CyclicReducedHolonomyDataMorphism

variable {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]

/-- Underlying isometric linear map of a cyclic reduced holonomy morphism. -/
def map {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) : H →ₗᵢ[ℝ] Y :=
  f.toReducedMorphism.map

/-- Identity morphism of a cyclic reduced holonomy datum. -/
def identity (X : CyclicReducedHolonomyData H) :
    CyclicReducedHolonomyDataMorphism X X where
  toReducedMorphism :=
    ReducedHolonomyDataMorphism.identity X.toReducedHolonomyData

/-- Composition of cyclic reduced holonomy datum morphisms. -/
def comp {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    {Zdata : CyclicReducedHolonomyData Z}
    (g : CyclicReducedHolonomyDataMorphism Ydata Zdata)
    (f : CyclicReducedHolonomyDataMorphism X Ydata) :
    CyclicReducedHolonomyDataMorphism X Zdata where
  toReducedMorphism :=
    ReducedHolonomyDataMorphism.comp g.toReducedMorphism f.toReducedMorphism

/-- Identity morphisms act as the identity on points. -/
theorem identity_map (X : CyclicReducedHolonomyData H) (x : H) :
    (identity X).map x = x :=
  ReducedHolonomyDataMorphism.identity_map X.toReducedHolonomyData x

/-- Composition acts as function composition on points. -/
theorem comp_map {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    {Zdata : CyclicReducedHolonomyData Z}
    (g : CyclicReducedHolonomyDataMorphism Ydata Zdata)
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp g f).map x = g.map (f.map x) :=
  ReducedHolonomyDataMorphism.comp_map g.toReducedMorphism f.toReducedMorphism x

/-- Left identity law for cyclic reduced holonomy morphisms, stated pointwise. -/
theorem identity_comp_map
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp (identity Ydata) f).map x = f.map x :=
  ReducedHolonomyDataMorphism.identity_comp_map f.toReducedMorphism x

/-- Right identity law for cyclic reduced holonomy morphisms, stated pointwise. -/
theorem comp_identity_map
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp f (identity X)).map x = f.map x :=
  ReducedHolonomyDataMorphism.comp_identity_map f.toReducedMorphism x

/-- Associativity of cyclic reduced holonomy morphism composition, stated
pointwise. -/
theorem comp_assoc_map
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {Wdata : CyclicReducedHolonomyData W}
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    {Zdata : CyclicReducedHolonomyData Z}
    (h : CyclicReducedHolonomyDataMorphism Zdata Wdata)
    (g : CyclicReducedHolonomyDataMorphism Ydata Zdata)
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (comp h (comp g f)).map x = (comp (comp h g) f).map x :=
  ReducedHolonomyDataMorphism.comp_assoc_map h.toReducedMorphism
    g.toReducedMorphism f.toReducedMorphism x

/-- Cyclic morphisms intertwine forward reduced holonomy orbits. -/
theorem map_comm_orbitNat
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    f.map (X.toReducedHolonomyData.orbitNat x n) =
      Ydata.toReducedHolonomyData.orbitNat (f.map x) n :=
  ReducedHolonomyDataMorphism.map_comm_orbitNat f.toReducedMorphism x n

/-- Cyclic morphisms preserve the reduced holonomy charge. -/
theorem charge_preserving
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.toReducedHolonomyData.charge (f.map x) =
      X.toReducedHolonomyData.charge x :=
  ReducedHolonomyDataMorphism.charge_preserving f.toReducedMorphism x

/-- The source period closes the image orbit in the target. -/
theorem source_period_image_orbit_closed
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.orbitNat (f.map x) (n + X.period) =
      Ydata.toReducedHolonomyData.orbitNat (f.map x) n := by
  rw [← f.map_comm_orbitNat x (n + X.period)]
  rw [← f.map_comm_orbitNat x n]
  rw [CyclicReducedHolonomyData.orbitNat_periodic X x n]

/-- The target period also closes every image orbit. -/
theorem target_period_image_orbit_closed
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.orbitNat (f.map x) (n + Ydata.period) =
      Ydata.toReducedHolonomyData.orbitNat (f.map x) n :=
  CyclicReducedHolonomyData.orbitNat_periodic Ydata (f.map x) n

/-- The reduced charge is constant along the mapped cyclic orbit. -/
theorem mapped_orbit_charge_constant
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.charge
      (Ydata.toReducedHolonomyData.orbitNat (f.map x) n) =
        X.toReducedHolonomyData.charge x :=
  ReducedHolonomyDataMorphism.mapped_orbit_charge_constant
    f.toReducedMorphism x n

end CyclicReducedHolonomyDataMorphism

/-- Paper-facing identity morphism of a cyclic reduced holonomy datum. -/
def finiteCyclicReducedHolonomyDataIdentityMorphism
    (X : CyclicReducedHolonomyData H) :
    CyclicReducedHolonomyDataMorphism X X :=
  CyclicReducedHolonomyDataMorphism.identity X

/-- Paper-facing composition of cyclic reduced holonomy datum morphisms. -/
def finiteCyclicReducedHolonomyDataMorphismComp
    {Z : Type*} [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    {Zdata : CyclicReducedHolonomyData Z}
    (g : CyclicReducedHolonomyDataMorphism Ydata Zdata)
    (f : CyclicReducedHolonomyDataMorphism X Ydata) :
    CyclicReducedHolonomyDataMorphism X Zdata :=
  CyclicReducedHolonomyDataMorphism.comp g f

/-- Paper-facing charge preservation for cyclic reduced holonomy morphisms. -/
theorem finiteCyclicReducedHolonomyDataMorphismChargePreserving
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.toReducedHolonomyData.charge (f.map x) =
      X.toReducedHolonomyData.charge x :=
  CyclicReducedHolonomyDataMorphism.charge_preserving f x

/-- Paper-facing statement that the source period closes the mapped orbit. -/
theorem finiteCyclicReducedHolonomyDataMorphismSourcePeriodImageOrbitClosed
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.orbitNat (f.map x) (n + X.period) =
      Ydata.toReducedHolonomyData.orbitNat (f.map x) n :=
  CyclicReducedHolonomyDataMorphism.source_period_image_orbit_closed f x n

/-- Paper-facing statement that the target period closes the mapped orbit. -/
theorem finiteCyclicReducedHolonomyDataMorphismTargetPeriodImageOrbitClosed
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.orbitNat (f.map x) (n + Ydata.period) =
      Ydata.toReducedHolonomyData.orbitNat (f.map x) n :=
  CyclicReducedHolonomyDataMorphism.target_period_image_orbit_closed f x n

/-- Paper-facing mapped cyclic orbit charge conservation. -/
theorem finiteCyclicReducedHolonomyDataMorphismMappedOrbitChargeConstant
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.charge
      (Ydata.toReducedHolonomyData.orbitNat (f.map x) n) =
        X.toReducedHolonomyData.charge x :=
  CyclicReducedHolonomyDataMorphism.mapped_orbit_charge_constant f x n

/-- Paper-facing left identity law for cyclic reduced holonomy datum morphisms. -/
theorem finiteCyclicReducedHolonomyDataMorphismLeftIdentityMap
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (CyclicReducedHolonomyDataMorphism.comp
      (CyclicReducedHolonomyDataMorphism.identity Ydata) f).map x = f.map x :=
  CyclicReducedHolonomyDataMorphism.identity_comp_map f x

/-- Paper-facing right identity law for cyclic reduced holonomy datum morphisms. -/
theorem finiteCyclicReducedHolonomyDataMorphismRightIdentityMap
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (CyclicReducedHolonomyDataMorphism.comp f
      (CyclicReducedHolonomyDataMorphism.identity X)).map x = f.map x :=
  CyclicReducedHolonomyDataMorphism.comp_identity_map f x

/-- Paper-facing associativity law for cyclic reduced holonomy datum morphism
composition. -/
theorem finiteCyclicReducedHolonomyDataMorphismAssocMap
    {Z W : Type*}
    [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    {Wdata : CyclicReducedHolonomyData W}
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    {Zdata : CyclicReducedHolonomyData Z}
    (h : CyclicReducedHolonomyDataMorphism Zdata Wdata)
    (g : CyclicReducedHolonomyDataMorphism Ydata Zdata)
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (CyclicReducedHolonomyDataMorphism.comp h
      (CyclicReducedHolonomyDataMorphism.comp g f)).map x =
        (CyclicReducedHolonomyDataMorphism.comp
          (CyclicReducedHolonomyDataMorphism.comp h g) f).map x :=
  CyclicReducedHolonomyDataMorphism.comp_assoc_map h g f x

end ReducedHolonomyNoether

/-! ### Finite non-abelian lift layer -/

/-- Group-valued link transport data for a chosen non-abelian lift.  The smooth
connection and exponential realization are deliberately outside this finite core. -/
structure NonabelianLift (K : FiniteTransportComplex V E F) (G : Type*) [Group G] where
  rho : E → G

namespace NonabelianLift

variable {G X : Type*} [Group G]

/-- Vertex frame change acting on a group-valued link. -/
def frameChange (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) : E → G :=
  fun e => (g (K.source e))⁻¹ * rho e * g (K.target e)

/-- Product of link transports along an edge list. -/
def edgeListHolonomy (rho : E → G) (edges : List E) : G :=
  (edges.map rho).prod

/-- A finite edge list is a path from `vStart` to `vEnd` when every edge starts
at the current vertex and the final current vertex is `vEnd`. -/
def IsEdgePathFrom (K : FiniteTransportComplex V E F)
    (vStart : V) : List E → V → Prop
  | [], vEnd => vEnd = vStart
  | e :: rest, vEnd => K.source e = vStart ∧ IsEdgePathFrom K (K.target e) rest vEnd

/-- A finite edge list is a closed loop based at `base`. -/
def IsClosedEdgeLoop (K : FiniteTransportComplex V E F)
    (base : V) (edges : List E) : Prop :=
  IsEdgePathFrom K base edges base

/-- Frame-conjugation identity for an actual finite edge path using the
`source` and `target` maps of the transport complex. -/
theorem edgeListHolonomy_frameChange_of_path
    (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) :
    ∀ {vStart vEnd : V} (edges : List E),
      IsEdgePathFrom K vStart edges vEnd →
        edgeListHolonomy (frameChange K rho g) edges =
          (g vStart)⁻¹ * edgeListHolonomy rho edges * g vEnd
  | vStart, vEnd, [], hpath => by
      simp [IsEdgePathFrom] at hpath
      simp [edgeListHolonomy, hpath]
  | vStart, vEnd, e :: rest, hpath => by
      rcases hpath with ⟨hsource, htail⟩
      have htailHol :=
        edgeListHolonomy_frameChange_of_path K rho g
          (vStart := K.target e) (vEnd := vEnd) rest htail
      simp [edgeListHolonomy] at htailHol
      simp [edgeListHolonomy, frameChange, hsource, htailHol, mul_assoc]

/-- Closed edge loops transform by conjugation at their base vertex. -/
theorem closedEdgeLoopHolonomy_frame_conjugate
    (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : IsClosedEdgeLoop K base edges) :
    edgeListHolonomy (frameChange K rho g) edges =
      (g base)⁻¹ * edgeListHolonomy rho edges * g base :=
  edgeListHolonomy_frameChange_of_path K rho g edges hclosed

/-- Algebraic path-step data used to prove the non-abelian frame-cancellation
identity without committing to a particular mesh API.  A step stores the link
transport and the frame at the next vertex. -/
abbrev FramedStep (G : Type*) := G × G

/-- Product of frame-transformed links along a path with a fixed starting frame. -/
def framedPathHolonomyFrom (gStart : G) : List (FramedStep G) → G
  | [] => 1
  | (rho, gNext) :: rest =>
      gStart⁻¹ * rho * gNext * framedPathHolonomyFrom gNext rest

/-- Ordinary link product underlying a framed path. -/
def pathHolonomyFromSteps : List (FramedStep G) → G :=
  fun steps => (steps.map Prod.fst).prod

/-- Final vertex frame of a framed path. -/
def finalFrameFrom (gStart : G) : List (FramedStep G) → G
  | [] => gStart
  | (_, gNext) :: rest => finalFrameFrom gNext rest

/-- Telescoping cancellation of intermediate frames along a path. -/
theorem framedPathHolonomyFrom_eq_conj_endpoints
    (gStart : G) (steps : List (FramedStep G)) :
    framedPathHolonomyFrom gStart steps =
      gStart⁻¹ * pathHolonomyFromSteps steps * finalFrameFrom gStart steps := by
  induction steps generalizing gStart with
  | nil =>
      simp [framedPathHolonomyFrom, pathHolonomyFromSteps, finalFrameFrom]
  | cons step rest ih =>
      rcases step with ⟨rho, gNext⟩
      simp [framedPathHolonomyFrom, pathHolonomyFromSteps, finalFrameFrom, ih,
        mul_assoc]

/-- Closed-loop frame change acts by conjugation at the base frame. -/
theorem closedLoopHolonomy_frame_conjugate
    (gBase : G) (steps : List (FramedStep G))
    (hclosed : finalFrameFrom gBase steps = gBase) :
    framedPathHolonomyFrom gBase steps =
      gBase⁻¹ * pathHolonomyFromSteps steps * gBase := by
  simpa [hclosed] using framedPathHolonomyFrom_eq_conj_endpoints
    (gStart := gBase) (steps := steps)

/-- A class function is invariant under conjugation. -/
def IsClassFunction (chi : G → X) : Prop :=
  ∀ g w : G, chi (g⁻¹ * w * g) = chi w

/-- Closed-loop class functions are invariant under vertex frame changes. -/
theorem closedLoopClassFunction_frame_invariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (gBase : G) (steps : List (FramedStep G))
    (hclosed : finalFrameFrom gBase steps = gBase) :
    chi (framedPathHolonomyFrom gBase steps) =
      chi (pathHolonomyFromSteps steps) := by
  rw [closedLoopHolonomy_frame_conjugate (gBase := gBase) (steps := steps) hclosed]
  exact hchi gBase (pathHolonomyFromSteps steps)

/-- Closed edge-loop class functions are invariant under vertex frame changes
for actual finite `source`/`target` edge paths. -/
theorem closedEdgeLoopClassFunction_frame_invariant
    (K : FiniteTransportComplex V E F)
    (chi : G → X) (hchi : IsClassFunction chi)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : IsClosedEdgeLoop K base edges) :
    chi (edgeListHolonomy (frameChange K rho g) edges) =
      chi (edgeListHolonomy rho edges) := by
  rw [closedEdgeLoopHolonomy_frame_conjugate K rho g base edges hclosed]
  exact hchi (g base) (edgeListHolonomy rho edges)

/-- Paper-facing closed-loop frame-conjugation identity for finite
non-abelian lifts. -/
theorem finiteNonabelianClosedLoopFrameConjugation
    (gBase : G) (steps : List (FramedStep G))
    (hclosed : finalFrameFrom gBase steps = gBase) :
    framedPathHolonomyFrom gBase steps =
      gBase⁻¹ * pathHolonomyFromSteps steps * gBase :=
  closedLoopHolonomy_frame_conjugate (gBase := gBase) (steps := steps) hclosed

/-- Paper-facing class-function invariance for finite closed non-abelian
loops. -/
theorem finiteNonabelianClosedLoopClassFunctionInvariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (gBase : G) (steps : List (FramedStep G))
    (hclosed : finalFrameFrom gBase steps = gBase) :
    chi (framedPathHolonomyFrom gBase steps) =
      chi (pathHolonomyFromSteps steps) :=
  closedLoopClassFunction_frame_invariant chi hchi gBase steps hclosed

/-- Paper-facing edge-path frame-conjugation identity for finite non-abelian
lifts over the actual source-target data of the complex. -/
theorem finiteNonabelianEdgePathFrameConjugation
    (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) (vStart vEnd : V) (edges : List E)
    (hpath : IsEdgePathFrom K vStart edges vEnd) :
    edgeListHolonomy (frameChange K rho g) edges =
      (g vStart)⁻¹ * edgeListHolonomy rho edges * g vEnd :=
  edgeListHolonomy_frameChange_of_path K rho g edges hpath

/-- Paper-facing closed edge-loop frame-conjugation identity for finite
non-abelian lifts over the actual source-target data of the complex. -/
theorem finiteNonabelianClosedEdgeLoopFrameConjugation
    (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : IsClosedEdgeLoop K base edges) :
    edgeListHolonomy (frameChange K rho g) edges =
      (g base)⁻¹ * edgeListHolonomy rho edges * g base :=
  closedEdgeLoopHolonomy_frame_conjugate K rho g base edges hclosed

/-- Paper-facing class-function invariance for finite closed edge loops over
the actual source-target data of the complex. -/
theorem finiteNonabelianClosedEdgeLoopClassFunctionInvariant
    (K : FiniteTransportComplex V E F)
    (chi : G → X) (hchi : IsClassFunction chi)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : IsClosedEdgeLoop K base edges) :
    chi (edgeListHolonomy (frameChange K rho g) edges) =
      chi (edgeListHolonomy rho edges) :=
  closedEdgeLoopClassFunction_frame_invariant K chi hchi rho g base edges hclosed

/-- A finite group word equipped with an explicit reduction-to-empty certificate.
This is the Lean-level version of the word-cancellation premise in the finite
cube/Bianchi identity. -/
inductive WordReducesToOne : List G → Prop
  | nil : WordReducesToOne []
  | cancel (x : G) (w : List G) :
      WordReducesToOne w → WordReducesToOne (x :: x⁻¹ :: w)
  | cancel_inv (x : G) (w : List G) :
      WordReducesToOne w → WordReducesToOne (x⁻¹ :: x :: w)
  | append {w₁ w₂ : List G} :
      WordReducesToOne w₁ → WordReducesToOne w₂ → WordReducesToOne (w₁ ++ w₂)
  | conjugate (x : G) {w : List G} :
      WordReducesToOne w → WordReducesToOne (x :: w ++ [x⁻¹])
  | cancel_middle (pre post : List G) (x : G) :
      WordReducesToOne (pre ++ post) → WordReducesToOne (pre ++ x :: x⁻¹ :: post)
  | cancel_inv_middle (pre post : List G) (x : G) :
      WordReducesToOne (pre ++ post) → WordReducesToOne (pre ++ x⁻¹ :: x :: post)

namespace WordReducesToOne

/-- Boundary normal form made of consecutive opposite-orientation pairs. -/
def pairedBoundaryWord : List G → List G
  | [] => []
  | x :: xs => x :: x⁻¹ :: pairedBoundaryWord xs

/-- Formal inverse word, in reverse order with inverted entries. -/
def inverseWord : List G → List G
  | [] => []
  | x :: xs => inverseWord xs ++ [x⁻¹]

/-- A word followed by its formal inverse reduces to the empty word. -/
theorem word_append_inverseWord_reduces (w : List G) :
    WordReducesToOne (G := G) (w ++ inverseWord (G := G) w) := by
  induction w with
  | nil =>
      exact WordReducesToOne.nil
  | cons x xs ih =>
      simpa [inverseWord, List.append_assoc] using WordReducesToOne.conjugate x ih

/-- A boundary word in consecutive opposite-orientation pairs reduces to the
empty word. -/
theorem pairedBoundaryWord_reduces (xs : List G) :
    WordReducesToOne (G := G) (pairedBoundaryWord xs) := by
  induction xs with
  | nil =>
      exact WordReducesToOne.nil
  | cons x xs ih =>
      exact WordReducesToOne.cancel x (pairedBoundaryWord xs) ih

/-- Evaluating a word with a reduction-to-empty certificate gives the identity. -/
theorem prod_eq_one {w : List G} (h : WordReducesToOne (G := G) w) :
    w.prod = 1 := by
  induction h with
  | nil =>
      simp
  | cancel x w h ih =>
      simp [ih]
  | cancel_inv x w h ih =>
      simp [ih]
  | append h₁ h₂ ih₁ ih₂ =>
      simp [List.prod_append, ih₁, ih₂]
  | conjugate x h ih =>
      simp [List.prod_append, ih]
  | cancel_middle pre post x h ih =>
      simp [List.prod_append]
      simpa [List.prod_append] using ih
  | cancel_inv_middle pre post x h ih =>
      simp [List.prod_append]
      simpa [List.prod_append] using ih

/-- Evaluation of a paired opposite-orientation boundary word. -/
theorem pairedBoundaryWord_prod_eq_one (xs : List G) :
    (pairedBoundaryWord (G := G) xs).prod = 1 :=
  prod_eq_one (pairedBoundaryWord_reduces (G := G) xs)

end WordReducesToOne

/-- A transported word followed by its formal inverse, based at a chosen tree
path.  This is the word-level form used when a whole face boundary is cancelled
against the reverse face boundary, rather than compressed to one face element. -/
def transportedWordWithInverse (tree : G) (faceWord : List G) : List G :=
  tree :: (faceWord ++ WordReducesToOne.inverseWord (G := G) faceWord) ++ [tree⁻¹]

/-- A transported word with its formal inverse has an explicit
reduction-to-empty certificate. -/
theorem transportedWordWithInverse_reduces (tree : G) (faceWord : List G) :
    WordReducesToOne (G := G) (transportedWordWithInverse tree faceWord) := by
  exact WordReducesToOne.conjugate tree
    (WordReducesToOne.word_append_inverseWord_reduces (G := G) faceWord)

/-- Evaluation of a transported word with its formal inverse. -/
theorem transportedWordWithInverse_prod_eq_one (tree : G) (faceWord : List G) :
    (transportedWordWithInverse (G := G) tree faceWord).prod = 1 :=
  WordReducesToOne.prod_eq_one (transportedWordWithInverse_reduces tree faceWord)

/-- Concatenation of transported word/formal-inverse pairs. -/
def transportedWordsWithInverses : List (G × List G) → List G
  | [] => []
  | pair :: rest =>
      transportedWordWithInverse pair.1 pair.2 ++ transportedWordsWithInverses rest

/-- Any finite concatenation of transported word/formal-inverse pairs reduces
to the empty word. -/
theorem transportedWordsWithInverses_reduces (pairs : List (G × List G)) :
    WordReducesToOne (G := G) (transportedWordsWithInverses pairs) := by
  induction pairs with
  | nil =>
      exact WordReducesToOne.nil
  | cons pair rest ih =>
      exact WordReducesToOne.append
        (transportedWordWithInverse_reduces pair.1 pair.2) ih

/-- Evaluation of a finite concatenation of transported word/formal-inverse
pairs. -/
theorem transportedWordsWithInverses_prod_eq_one (pairs : List (G × List G)) :
    (transportedWordsWithInverses (G := G) pairs).prod = 1 :=
  WordReducesToOne.prod_eq_one (transportedWordsWithInverses_reduces pairs)

/-- Canonical six-face cube boundary word after tree transports and immediate
tree-edge cancellations have put the remaining opposite-oriented face
contributions in adjacent pairs. -/
def cubeOppositeFaceBoundaryWord (xy yz zx : G) : List G :=
  [xy, xy⁻¹, yz, yz⁻¹, zx, zx⁻¹]

/-- A based opposite-face pair after transport along a spanning-tree word. -/
def transportedOppositeFacePair (tree face : G) : List G :=
  [tree, face, face⁻¹, tree⁻¹]

/-- A transported opposite-face pair reduces by first cancelling the face pair
and then the tree transport with its inverse. -/
theorem transportedOppositeFacePair_reduces (tree face : G) :
    WordReducesToOne (G := G) (transportedOppositeFacePair tree face) := by
  exact WordReducesToOne.conjugate tree
    (WordReducesToOne.cancel face [] WordReducesToOne.nil)

/-- Evaluation of a transported opposite-face pair. -/
theorem transportedOppositeFacePair_prod_eq_one (tree face : G) :
    (transportedOppositeFacePair tree face).prod = 1 :=
  WordReducesToOne.prod_eq_one (transportedOppositeFacePair_reduces tree face)

/-- Cube boundary word after each opposite face-pair has been transported to a
common base vertex through a chosen tree path. -/
def transportedCubeOppositeFaceBoundaryWord
    (xy yz zx treeXY treeYZ treeZX : G) : List G :=
  transportedOppositeFacePair treeXY xy ++
    transportedOppositeFacePair treeYZ yz ++
      transportedOppositeFacePair treeZX zx

/-- The tree-transported six-face cube word has an explicit reduction-to-empty
certificate. -/
theorem transportedCubeOppositeFaceBoundaryWord_reduces
    (xy yz zx treeXY treeYZ treeZX : G) :
    WordReducesToOne (G := G)
      (transportedCubeOppositeFaceBoundaryWord xy yz zx treeXY treeYZ treeZX) := by
  exact WordReducesToOne.append
    (WordReducesToOne.append
      (transportedOppositeFacePair_reduces treeXY xy)
      (transportedOppositeFacePair_reduces treeYZ yz))
    (transportedOppositeFacePair_reduces treeZX zx)

/-- Tree-transported six-face cube/Bianchi normal form. -/
theorem transportedCubeOppositeFaceBoundaryWord_prod_eq_one
    (xy yz zx treeXY treeYZ treeZX : G) :
    (transportedCubeOppositeFaceBoundaryWord xy yz zx treeXY treeYZ treeZX).prod = 1 :=
  WordReducesToOne.prod_eq_one
    (transportedCubeOppositeFaceBoundaryWord_reduces xy yz zx treeXY treeYZ treeZX)

/-- Twelve positively oriented edge holonomies of a combinatorial cube.  The
field name records the coordinate direction and the fixed coordinates of the
edge, for example `x_y1_z0` is the positive `x`-edge at `y=1,z=0`. -/
structure CubeEdgeHolonomies (G : Type*) where
  x_y0_z0 : G
  x_y1_z0 : G
  x_y0_z1 : G
  x_y1_z1 : G
  y_x0_z0 : G
  y_x1_z0 : G
  y_x0_z1 : G
  y_x1_z1 : G
  z_x0_y0 : G
  z_x1_y0 : G
  z_x0_y1 : G
  z_x1_y1 : G

namespace CubeEdgeHolonomies

/-- Vertex frame data on the eight vertices of a combinatorial cube. -/
structure CubeVertexFrames (G : Type*) where
  v000 : G
  v100 : G
  v010 : G
  v110 : G
  v001 : G
  v101 : G
  v011 : G
  v111 : G

/-- Edge-wise cube frame change for the twelve positive cube-edge transports. -/
def frameChange (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    CubeEdgeHolonomies G where
  x_y0_z0 := Γ.v000⁻¹ * C.x_y0_z0 * Γ.v100
  x_y1_z0 := Γ.v010⁻¹ * C.x_y1_z0 * Γ.v110
  x_y0_z1 := Γ.v001⁻¹ * C.x_y0_z1 * Γ.v101
  x_y1_z1 := Γ.v011⁻¹ * C.x_y1_z1 * Γ.v111
  y_x0_z0 := Γ.v000⁻¹ * C.y_x0_z0 * Γ.v010
  y_x1_z0 := Γ.v100⁻¹ * C.y_x1_z0 * Γ.v110
  y_x0_z1 := Γ.v001⁻¹ * C.y_x0_z1 * Γ.v011
  y_x1_z1 := Γ.v101⁻¹ * C.y_x1_z1 * Γ.v111
  z_x0_y0 := Γ.v000⁻¹ * C.z_x0_y0 * Γ.v001
  z_x1_y0 := Γ.v100⁻¹ * C.z_x1_y0 * Γ.v101
  z_x0_y1 := Γ.v010⁻¹ * C.z_x0_y1 * Γ.v011
  z_x1_y1 := Γ.v110⁻¹ * C.z_x1_y1 * Γ.v111

/-- Oriented lower `z=0` face word. -/
def faceZ0 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0, C.y_x1_z0, C.x_y1_z0⁻¹, C.y_x0_z0⁻¹]

/-- Oriented upper `z=1` face word, with the opposite boundary orientation. -/
def faceZ1 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z1⁻¹, C.y_x0_z1, C.x_y1_z1, C.y_x1_z1⁻¹]

/-- Oriented `x=0` face word. -/
def faceX0 (C : CubeEdgeHolonomies G) : List G :=
  [C.y_x0_z0, C.z_x0_y1, C.y_x0_z1⁻¹, C.z_x0_y0⁻¹]

/-- Oriented `x=1` face word, with the opposite boundary orientation. -/
def faceX1 (C : CubeEdgeHolonomies G) : List G :=
  [C.y_x1_z0⁻¹, C.z_x1_y0, C.y_x1_z1, C.z_x1_y1⁻¹]

/-- Oriented `y=0` face word. -/
def faceY0 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0⁻¹, C.z_x0_y0, C.x_y0_z1, C.z_x1_y0⁻¹]

/-- Oriented `y=1` face word, with the opposite boundary orientation. -/
def faceY1 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y1_z0, C.z_x1_y1, C.x_y1_z1⁻¹, C.z_x0_y1⁻¹]

/-- The six concrete face words of the combinatorial cube. -/
def faceBoundaryWords (C : CubeEdgeHolonomies G) : List (List G) :=
  [faceZ0 C, faceZ1 C, faceX0 C, faceX1 C, faceY0 C, faceY1 C]

/-- Tree path from the base vertex `000` to the basepoint of the upper `z=1` face. -/
def pathToFaceZ1 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0, C.z_x1_y0]

/-- Tree path from the base vertex `000` to the basepoint of the `x=1` face. -/
def pathToFaceX1 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0, C.y_x1_z0]

/-- Tree path from the base vertex `000` to the basepoint of the `y=0` face. -/
def pathToFaceY0 (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0]

/-- Tree path from the base vertex `000` to the basepoint of the `y=1` face. -/
def pathToFaceY1 (C : CubeEdgeHolonomies G) : List G :=
  [C.y_x0_z0]

/-- A face word transported to the common base vertex along a tree path. -/
def basedFaceWord (path faceWord : List G) : List G :=
  path ++ faceWord ++ WordReducesToOne.inverseWord (G := G) path

/-- Lower `z=0` face word based at the common cube base vertex. -/
def basedFaceZ0Word (C : CubeEdgeHolonomies G) : List G :=
  faceZ0 C

/-- Upper `y=1` face word transported to the common cube base vertex. -/
def basedFaceY1Word (C : CubeEdgeHolonomies G) : List G :=
  basedFaceWord (pathToFaceY1 C) (faceY1 C)

/-- Lower `x=0` face word based at the common cube base vertex. -/
def basedFaceX0Word (C : CubeEdgeHolonomies G) : List G :=
  faceX0 C

/-- Lower `y=0` face word transported to the common cube base vertex. -/
def basedFaceY0Word (C : CubeEdgeHolonomies G) : List G :=
  basedFaceWord (pathToFaceY0 C) (faceY0 C)

/-- Upper `z=1` face word transported to the common cube base vertex. -/
def basedFaceZ1Word (C : CubeEdgeHolonomies G) : List G :=
  basedFaceWord (pathToFaceZ1 C) (faceZ1 C)

/-- Upper `x=1` face word transported to the common cube base vertex. -/
def basedFaceX1Word (C : CubeEdgeHolonomies G) : List G :=
  basedFaceWord (pathToFaceX1 C) (faceX1 C)

/-- Concrete based cube-boundary word.  The order is the free-word normal form
`z=0`, `y=1`, `x=0`, `y=0`, `z=1`, `x=1`; the nontrivial face basepoints are
transported to the base vertex `000` by the displayed tree paths. -/
def basedCubeBoundaryWord (C : CubeEdgeHolonomies G) : List G :=
  faceZ0 C ++
    basedFaceWord (pathToFaceY1 C) (faceY1 C) ++
      faceX0 C ++
        basedFaceWord (pathToFaceY0 C) (faceY0 C) ++
          basedFaceWord (pathToFaceZ1 C) (faceZ1 C) ++
            basedFaceWord (pathToFaceX1 C) (faceX1 C)

/-- The concrete based cube-boundary word freely reduces to the empty word. -/
theorem basedCubeBoundaryWord_reduces (C : CubeEdgeHolonomies G) :
    WordReducesToOne (G := G) (basedCubeBoundaryWord C) := by
  let x00 := C.x_y0_z0
  let x10 := C.x_y1_z0
  let x01 := C.x_y0_z1
  let x11 := C.x_y1_z1
  let y00 := C.y_x0_z0
  let y10 := C.y_x1_z0
  let y01 := C.y_x0_z1
  let y11 := C.y_x1_z1
  let z00 := C.z_x0_y0
  let z10 := C.z_x1_y0
  let z01 := C.z_x0_y1
  let z11 := C.z_x1_y1
  change WordReducesToOne (G := G)
    [x00, y10, x10⁻¹, y00⁻¹, y00, x10, z11, x11⁻¹, z01⁻¹, y00⁻¹, y00, z01,
      y01⁻¹, z00⁻¹, x00, x00⁻¹, z00, x01, z10⁻¹, x00⁻¹, x00, z10,
      x01⁻¹, y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11,
      z11⁻¹, y10⁻¹, x00⁻¹]
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, x10⁻¹]
    [x10, z11, x11⁻¹, z01⁻¹, y00⁻¹, y00, z01, y01⁻¹, z00⁻¹, x00, x00⁻¹,
      z00, x01, z10⁻¹, x00⁻¹, x00, z10, x01⁻¹, y01, x11, y11⁻¹, z10⁻¹,
      x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    y00 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10]
    [z11, x11⁻¹, z01⁻¹, y00⁻¹, y00, z01, y01⁻¹, z00⁻¹, x00, x00⁻¹, z00,
      x01, z10⁻¹, x00⁻¹, x00, z10, x01⁻¹, y01, x11, y11⁻¹, z10⁻¹,
      x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    x10 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹, z01⁻¹]
    [z01, y01⁻¹, z00⁻¹, x00, x00⁻¹, z00, x01, z10⁻¹, x00⁻¹, x00, z10,
      x01⁻¹, y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11,
      z11⁻¹, y10⁻¹, x00⁻¹]
    y00 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹]
    [y01⁻¹, z00⁻¹, x00, x00⁻¹, z00, x01, z10⁻¹, x00⁻¹, x00, z10, x01⁻¹,
      y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹,
      y10⁻¹, x00⁻¹]
    z01 ?_
  refine WordReducesToOne.cancel_middle
    [x00, y10, z11, x11⁻¹, y01⁻¹, z00⁻¹]
    [z00, x01, z10⁻¹, x00⁻¹, x00, z10, x01⁻¹, y01, x11, y11⁻¹, z10⁻¹,
      x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    x00 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹, y01⁻¹]
    [x01, z10⁻¹, x00⁻¹, x00, z10, x01⁻¹, y01, x11, y11⁻¹, z10⁻¹, x00⁻¹,
      x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    z00 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹, y01⁻¹, x01, z10⁻¹]
    [z10, x01⁻¹, y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11,
      z11⁻¹, y10⁻¹, x00⁻¹]
    x00 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹, y01⁻¹, x01]
    [x01⁻¹, y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11,
      z11⁻¹, y10⁻¹, x00⁻¹]
    z10 ?_
  refine WordReducesToOne.cancel_middle
    [x00, y10, z11, x11⁻¹, y01⁻¹]
    [y01, x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹,
      y10⁻¹, x00⁻¹]
    x01 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, x11⁻¹]
    [x11, y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹,
      x00⁻¹]
    y01 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11]
    [y11⁻¹, z10⁻¹, x00⁻¹, x00, y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    x11 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, y11⁻¹, z10⁻¹]
    [y10, y10⁻¹, z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    x00 ?_
  refine WordReducesToOne.cancel_middle
    [x00, y10, z11, y11⁻¹, z10⁻¹]
    [z10, y11, z11⁻¹, y10⁻¹, x00⁻¹]
    y10 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11, y11⁻¹]
    [y11, z11⁻¹, y10⁻¹, x00⁻¹]
    z10 ?_
  refine WordReducesToOne.cancel_inv_middle
    [x00, y10, z11]
    [z11⁻¹, y10⁻¹, x00⁻¹]
    y11 ?_
  refine WordReducesToOne.cancel_middle
    [x00, y10]
    [y10⁻¹, x00⁻¹]
    z11 ?_
  refine WordReducesToOne.cancel_middle
    [x00]
    [x00⁻¹]
    y10 ?_
  refine WordReducesToOne.cancel_middle
    []
    []
    x00 ?_
  exact WordReducesToOne.nil

/-- Evaluation of the concrete based cube-boundary word. -/
theorem basedCubeBoundaryWord_prod_eq_one (C : CubeEdgeHolonomies G) :
    (basedCubeBoundaryWord C).prod = 1 :=
  WordReducesToOne.prod_eq_one (basedCubeBoundaryWord_reduces C)

/-- The same concrete cube-boundary word, written explicitly as the ordered
product of the six named based face words. -/
def sixBasedFaceBoundaryWord (C : CubeEdgeHolonomies G) : List G :=
  basedFaceZ0Word C ++
    basedFaceY1Word C ++
      basedFaceX0Word C ++
        basedFaceY0Word C ++
          basedFaceZ1Word C ++
            basedFaceX1Word C

/-- The six named based face words unfold to the concrete based cube-boundary
word used in the reduction proof. -/
theorem sixBasedFaceBoundaryWord_eq_basedCubeBoundaryWord
    (C : CubeEdgeHolonomies G) :
    sixBasedFaceBoundaryWord C = basedCubeBoundaryWord C :=
  rfl

/-- The six named based face words freely reduce to the empty word. -/
theorem sixBasedFaceBoundaryWord_reduces (C : CubeEdgeHolonomies G) :
    WordReducesToOne (G := G) (sixBasedFaceBoundaryWord C) := by
  rw [sixBasedFaceBoundaryWord_eq_basedCubeBoundaryWord]
  exact basedCubeBoundaryWord_reduces C

/-- Exact based cube-boundary identity for the six named based face words. -/
theorem exactBasedCubeBoundaryIdentity (C : CubeEdgeHolonomies G) :
    (sixBasedFaceBoundaryWord C).prod = 1 := by
  rw [sixBasedFaceBoundaryWord_eq_basedCubeBoundaryWord]
  exact basedCubeBoundaryWord_prod_eq_one C

/-- The six based face holonomies as group elements, in the same order as the
based cube-boundary word. -/
def basedFaceHolonomyProducts (C : CubeEdgeHolonomies G) : List G :=
  [(basedFaceZ0Word C).prod,
   (basedFaceY1Word C).prod,
   (basedFaceX0Word C).prod,
   (basedFaceY0Word C).prod,
   (basedFaceZ1Word C).prod,
   (basedFaceX1Word C).prod]

/-- Multiplying the six based face holonomies is the same as evaluating their
concatenated based cube-boundary word. -/
theorem basedFaceHolonomyProducts_prod_eq_boundaryWord_prod
    (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts C).prod = (sixBasedFaceBoundaryWord C).prod := by
  simp [basedFaceHolonomyProducts, sixBasedFaceBoundaryWord, List.prod_append]

/-- Concrete product form of the finite cube/Bianchi identity: the ordered
product of the six based face holonomies is the identity. -/
theorem basedFaceHolonomyProducts_prod_eq_one
    (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts C).prod = 1 := by
  rw [basedFaceHolonomyProducts_prod_eq_boundaryWord_prod]
  exact exactBasedCubeBoundaryIdentity C

/-- Paper-facing evaluation equivalence between the six based face holonomies
and the concatenated based cube-boundary word. -/
theorem finiteCubeBasedFaceHolonomyProductBoundaryEvaluation
    (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts C).prod = (sixBasedFaceBoundaryWord C).prod :=
  basedFaceHolonomyProducts_prod_eq_boundaryWord_prod C

/-- Paper-facing product form of the finite cube/Bianchi identity. -/
theorem finiteCubeBasedFaceHolonomyProductIdentity
    (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts C).prod = 1 :=
  basedFaceHolonomyProducts_prod_eq_one C

/-- The lower `z=0` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceZ0Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceZ0Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceZ0Word C).prod * Γ.v000 := by
  simp [basedFaceZ0Word, faceZ0, frameChange, mul_assoc]

/-- The upper `y=1` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceY1Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceY1Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceY1Word C).prod * Γ.v000 := by
  simp [basedFaceY1Word, basedFaceWord, pathToFaceY1, faceY1, frameChange,
    WordReducesToOne.inverseWord, mul_assoc]

/-- The lower `x=0` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceX0Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceX0Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceX0Word C).prod * Γ.v000 := by
  simp [basedFaceX0Word, faceX0, frameChange, mul_assoc]

/-- The lower `y=0` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceY0Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceY0Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceY0Word C).prod * Γ.v000 := by
  simp [basedFaceY0Word, basedFaceWord, pathToFaceY0, faceY0, frameChange,
    WordReducesToOne.inverseWord, mul_assoc]

/-- The upper `z=1` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceZ1Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceZ1Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceZ1Word C).prod * Γ.v000 := by
  simp [basedFaceZ1Word, basedFaceWord, pathToFaceZ1, faceZ1, frameChange,
    WordReducesToOne.inverseWord, mul_assoc]

/-- The upper `x=1` based face holonomy transforms by conjugation at the cube
base vertex. -/
theorem basedFaceX1Word_frameChange_prod
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceX1Word (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceX1Word C).prod * Γ.v000 := by
  simp [basedFaceX1Word, basedFaceWord, pathToFaceX1, faceX1, frameChange,
    WordReducesToOne.inverseWord, mul_assoc]

/-- The whole based cube-boundary word transforms by conjugation at the common
cube base vertex. -/
theorem basedCubeBoundaryWord_frameChange_conj
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedCubeBoundaryWord (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedCubeBoundaryWord C).prod * Γ.v000 := by
  simp [basedCubeBoundaryWord, basedFaceWord, pathToFaceY1, pathToFaceY0,
    pathToFaceZ1, pathToFaceX1, faceZ0, faceY1, faceX0, faceY0, faceZ1,
    faceX1, frameChange, WordReducesToOne.inverseWord, mul_assoc]

/-- Class functions of the based cube-boundary holonomy are invariant under
vertex frame changes. -/
theorem basedCubeBoundaryWord_frameChange_classFunction_invariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((basedCubeBoundaryWord (frameChange Γ C)).prod) =
      chi ((basedCubeBoundaryWord C).prod) := by
  rw [basedCubeBoundaryWord_frameChange_conj]
  exact hchi Γ.v000 ((basedCubeBoundaryWord C).prod)

/-- The based cube-boundary identity is stable under arbitrary vertex frame
changes of the twelve cube-edge transports. -/
theorem basedCubeBoundaryWord_frameChange_prod_eq_one
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedCubeBoundaryWord (frameChange Γ C)).prod = 1 :=
  basedCubeBoundaryWord_prod_eq_one (frameChange Γ C)

/-- The six named based face words transform by conjugation at the common cube
base vertex under arbitrary vertex frame changes. -/
theorem sixBasedFaceBoundaryWord_frameChange_conj
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (sixBasedFaceBoundaryWord (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (sixBasedFaceBoundaryWord C).prod * Γ.v000 := by
  rw [sixBasedFaceBoundaryWord_eq_basedCubeBoundaryWord]
  rw [sixBasedFaceBoundaryWord_eq_basedCubeBoundaryWord]
  exact basedCubeBoundaryWord_frameChange_conj Γ C

/-- The product of the six based face holonomies transforms by conjugation at
the common cube base vertex. -/
theorem basedFaceHolonomyProducts_frameChange_conj
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceHolonomyProducts C).prod * Γ.v000 := by
  rw [basedFaceHolonomyProducts_prod_eq_boundaryWord_prod]
  rw [basedFaceHolonomyProducts_prod_eq_boundaryWord_prod]
  exact sixBasedFaceBoundaryWord_frameChange_conj Γ C

/-- Class functions of the six-face based cube-boundary holonomy are invariant
under arbitrary vertex frame changes. -/
theorem sixBasedFaceBoundaryWord_frameChange_classFunction_invariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((sixBasedFaceBoundaryWord (frameChange Γ C)).prod) =
      chi ((sixBasedFaceBoundaryWord C).prod) := by
  rw [sixBasedFaceBoundaryWord_frameChange_conj]
  exact hchi Γ.v000 ((sixBasedFaceBoundaryWord C).prod)

/-- Class functions of the product of six based face holonomies are invariant
under arbitrary vertex frame changes. -/
theorem basedFaceHolonomyProducts_frameChange_classFunction_invariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts (frameChange Γ C)).prod) =
      chi ((basedFaceHolonomyProducts C).prod) := by
  rw [basedFaceHolonomyProducts_frameChange_conj]
  exact hchi Γ.v000 ((basedFaceHolonomyProducts C).prod)

/-- The product identity for the six based face holonomies is stable under
arbitrary cube vertex frame changes. -/
theorem basedFaceHolonomyProducts_frameChange_prod_eq_one
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts (frameChange Γ C)).prod = 1 :=
  basedFaceHolonomyProducts_prod_eq_one (frameChange Γ C)

/-- Any observable evaluated on the product of the six based face holonomies
equals its value at the identity element. -/
theorem basedFaceHolonomyProducts_eval_eq_identity
    (chi : G → X) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts C).prod) = chi 1 := by
  rw [basedFaceHolonomyProducts_prod_eq_one]

/-- Any observable evaluated on the frame-changed product of the six based face
holonomies equals its value at the identity element. -/
theorem basedFaceHolonomyProducts_frameChange_eval_eq_identity
    (chi : G → X) (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts (frameChange Γ C)).prod) = chi 1 := by
  rw [basedFaceHolonomyProducts_frameChange_prod_eq_one]

/-- The exact based cube-boundary identity for the six named based face words is
stable under arbitrary vertex frame changes. -/
theorem exactBasedCubeBoundaryIdentity_frameChange
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (sixBasedFaceBoundaryWord (frameChange Γ C)).prod = 1 :=
  exactBasedCubeBoundaryIdentity (frameChange Γ C)

/-- Paper-facing frame-change conjugation law for the product of the six based
face holonomies. -/
theorem finiteCubeBasedFaceHolonomyProductFrameChangeConjugation
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts (frameChange Γ C)).prod =
      Γ.v000⁻¹ * (basedFaceHolonomyProducts C).prod * Γ.v000 :=
  basedFaceHolonomyProducts_frameChange_conj Γ C

/-- Paper-facing class-function invariance for the product of the six based
face holonomies under cube vertex frame changes. -/
theorem finiteCubeBasedFaceHolonomyProductClassFunctionInvariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts (frameChange Γ C)).prod) =
      chi ((basedFaceHolonomyProducts C).prod) :=
  basedFaceHolonomyProducts_frameChange_classFunction_invariant chi hchi Γ C

/-- Paper-facing frame-stability of the finite cube/Bianchi product identity. -/
theorem finiteCubeBasedFaceHolonomyProductFrameChangeIdentity
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (basedFaceHolonomyProducts (frameChange Γ C)).prod = 1 :=
  basedFaceHolonomyProducts_frameChange_prod_eq_one Γ C

/-- Paper-facing evaluation of the finite cube/Bianchi product at the group
identity. -/
theorem finiteCubeBasedFaceHolonomyProductObservableAtIdentity
    (chi : G → X) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts C).prod) = chi 1 :=
  basedFaceHolonomyProducts_eval_eq_identity chi C

/-- Paper-facing evaluation of the frame-changed finite cube/Bianchi product at
the group identity. -/
theorem finiteCubeBasedFaceHolonomyProductFrameChangeObservableAtIdentity
    (chi : G → X) (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((basedFaceHolonomyProducts (frameChange Γ C)).prod) = chi 1 :=
  basedFaceHolonomyProducts_frameChange_eval_eq_identity chi Γ C

/-- The six concrete face words with chosen basepoint tree transports. -/
def faceBoundaryWordsWithTrees
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) : List (G × List G) :=
  [(treeZ0, faceZ0 C), (treeZ1, faceZ1 C),
   (treeX0, faceX0 C), (treeX1, faceX1 C),
   (treeY0, faceY0 C), (treeY1, faceY1 C)]

/-- Concrete cube face-boundary word in which each transported face word is
paired with its formal reverse face word. -/
def transportedFaceBoundaryWithFormalInverses
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) : List G :=
  transportedWordsWithInverses
    (faceBoundaryWordsWithTrees C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1)

/-- The concrete six-face word with formal reverse face words reduces to the
empty word. -/
theorem transportedFaceBoundaryWithFormalInverses_reduces
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) :
    WordReducesToOne (G := G)
      (transportedFaceBoundaryWithFormalInverses
        C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1) :=
  transportedWordsWithInverses_reduces
    (faceBoundaryWordsWithTrees C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1)

/-- Evaluation of the concrete six-face word with formal reverse face words. -/
theorem transportedFaceBoundaryWithFormalInverses_prod_eq_one
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) :
    (transportedFaceBoundaryWithFormalInverses
      C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1).prod = 1 :=
  WordReducesToOne.prod_eq_one
    (transportedFaceBoundaryWithFormalInverses_reduces
      C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1)

/-- Paper-facing reduction certificate for the concrete six-face word with
formal reverse face words. -/
theorem finiteCubeTransportedFaceBoundaryWithFormalInversesReduction
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) :
    WordReducesToOne (G := G)
      (transportedFaceBoundaryWithFormalInverses
        C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1) :=
  transportedFaceBoundaryWithFormalInverses_reduces
    C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1

/-- Paper-facing product identity for the concrete six-face word with formal
reverse face words. -/
theorem finiteCubeTransportedFaceBoundaryWithFormalInversesIdentity
    (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) :
    (transportedFaceBoundaryWithFormalInverses
      C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1).prod = 1 :=
  transportedFaceBoundaryWithFormalInverses_prod_eq_one
    C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1

/-- Paper-facing observable evaluation for the concrete six-face word with
formal reverse face words. -/
theorem finiteCubeTransportedFaceBoundaryWithFormalInversesObservableAtIdentity
    (chi : G → X) (C : CubeEdgeHolonomies G)
    (treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1 : G) :
    chi ((transportedFaceBoundaryWithFormalInverses
      C treeZ0 treeZ1 treeX0 treeX1 treeY0 treeY1).prod) = chi 1 := by
  rw [transportedFaceBoundaryWithFormalInverses_prod_eq_one]

/-- The twelve positive edge generators of the cube. -/
def boundaryEdgeGenerators (C : CubeEdgeHolonomies G) : List G :=
  [C.x_y0_z0, C.x_y1_z0, C.x_y0_z1, C.x_y1_z1,
   C.y_x0_z0, C.y_x1_z0, C.y_x0_z1, C.y_x1_z1,
   C.z_x0_y0, C.z_x1_y0, C.z_x0_y1, C.z_x1_y1]

/-- Edge-balanced normal form of the expanded cube boundary: each of the twelve
boundary edges occurs once with positive and once with negative orientation. -/
def boundaryEdgeNormalWord (C : CubeEdgeHolonomies G) : List G :=
  WordReducesToOne.pairedBoundaryWord (G := G) (boundaryEdgeGenerators C)

/-- The edge-balanced cube boundary normal form reduces to the empty word. -/
theorem boundaryEdgeNormalWord_reduces (C : CubeEdgeHolonomies G) :
    WordReducesToOne (G := G) (boundaryEdgeNormalWord C) :=
  WordReducesToOne.pairedBoundaryWord_reduces (G := G) (boundaryEdgeGenerators C)

/-- The edge-balanced 12-edge cube boundary evaluates to the group identity. -/
theorem boundaryEdgeNormalWord_prod_eq_one (C : CubeEdgeHolonomies G) :
    (boundaryEdgeNormalWord C).prod = 1 :=
  WordReducesToOne.prod_eq_one (boundaryEdgeNormalWord_reduces C)

/-- The edge-balanced cube normal form is also stable under arbitrary vertex
frame changes of the cube-edge transports. -/
theorem boundaryEdgeNormalWord_frameChange_prod_eq_one
    (Γ : CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (boundaryEdgeNormalWord (frameChange Γ C)).prod = 1 :=
  boundaryEdgeNormalWord_prod_eq_one (frameChange Γ C)

end CubeEdgeHolonomies

/-- The canonical six-face cube boundary word has an explicit reduction-to-empty
certificate. -/
theorem cubeOppositeFaceBoundaryWord_reduces (xy yz zx : G) :
    WordReducesToOne (G := G) (cubeOppositeFaceBoundaryWord xy yz zx) := by
  exact WordReducesToOne.cancel xy [yz, yz⁻¹, zx, zx⁻¹]
    (WordReducesToOne.cancel yz [zx, zx⁻¹]
      (WordReducesToOne.cancel zx [] WordReducesToOne.nil))

/-- Concrete six-face cube/Bianchi normal form: three opposite oriented face
pairs evaluate to the group identity. -/
theorem cubeOppositeFaceBoundaryWord_prod_eq_one (xy yz zx : G) :
    (cubeOppositeFaceBoundaryWord xy yz zx).prod = 1 :=
  WordReducesToOne.prod_eq_one (cubeOppositeFaceBoundaryWord_reduces xy yz zx)

/-- Six-face form with named opposite faces.  The hypotheses express that each
minus-oriented based face holonomy is the inverse of its plus-oriented partner. -/
theorem cubeBoundaryIdentity_of_oppositeFaces
    (xyPlus xyMinus yzPlus yzMinus zxPlus zxMinus : G)
    (hxy : xyMinus = xyPlus⁻¹)
    (hyz : yzMinus = yzPlus⁻¹)
    (hzx : zxMinus = zxPlus⁻¹) :
    ([xyPlus, xyMinus, yzPlus, yzMinus, zxPlus, zxMinus] : List G).prod = 1 := by
  subst xyMinus
  subst yzMinus
  subst zxMinus
  exact cubeOppositeFaceBoundaryWord_prod_eq_one xyPlus yzPlus zxPlus

/-- Exact finite-lattice Bianchi word identity from a cube-boundary cancellation
certificate.  A concrete cube supplies the word and this certificate; the group
evaluation then closes mechanically. -/
theorem cubeBoundaryIdentity_of_wordReduction
    (boundaryWord : List G) (hred : WordReducesToOne (G := G) boundaryWord) :
    boundaryWord.prod = 1 :=
  WordReducesToOne.prod_eq_one hred

/-! ### Algebraic plaquette curvature core -/

noncomputable section PlaquetteAlgebra

/-- Algebraic commutator in a noncommutative additive ring. -/
def algebraicCommutator {A : Type*} [NonUnitalNonAssocRing A] (X Y : A) : A :=
  X * Y - Y * X

variable {A : Type*} [NonUnitalNonAssocRing A]

/-- The six ordered pair commutators from the oriented four-edge word
`X, Y, -X, -Y` collapse to twice the basic commutator. -/
theorem fourIncrementCommutatorSignSum (X Y : A) :
    algebraicCommutator X Y + algebraicCommutator X (-X) + algebraicCommutator X (-Y) +
      algebraicCommutator Y (-X) + algebraicCommutator Y (-Y) +
        algebraicCommutator (-X) (-Y) =
          (2 : ℤ) • algebraicCommutator X Y := by
  simp only [algebraicCommutator]
  noncomm_ring

/-- Twice the quadratic self contribution of the four formal exponential factors
with first-order increments `X, Y, -X, -Y`.  The doubled form avoids choosing a
field inverse for the purely algebraic identity. -/
def doubledQuadraticSelfContribution (X Y : A) : A :=
  X * X + Y * Y + (-X) * (-X) + (-Y) * (-Y)

/-- Ordered pair contribution from multiplying four formal first-order factors
with increments `X, Y, -X, -Y`. -/
def orderedPairContribution (X Y : A) : A :=
  X * Y + X * (-X) + X * (-Y) + Y * (-X) + Y * (-Y) + (-X) * (-Y)

/-- The second-order product coefficient of the four-edge plaquette is the
commutator, written in doubled form: self quadratic terms plus twice the ordered
pair terms equal twice `[X,Y]`. -/
theorem doubledQuadraticPlaquetteContribution (X Y : A) :
    doubledQuadraticSelfContribution X Y + (2 : ℤ) • orderedPairContribution X Y =
      (2 : ℤ) • algebraicCommutator X Y := by
  simp only [doubledQuadraticSelfContribution, orderedPairContribution, algebraicCommutator]
  noncomm_ring

/-- Matrix commutator for finite-dimensional complex transport matrices. -/
def matrixCommutator {n : Type*} [Fintype n]
    (A B : Matrix n n ℂ) : Matrix n n ℂ :=
  algebraicCommutator A B

variable {n : Type*} [Fintype n]

lemma matrixCommutator_smul (c d : ℂ) (A B : Matrix n n ℂ) :
    matrixCommutator (c • A) (d • B) = (c * d) • matrixCommutator A B := by
  simp [matrixCommutator, algebraicCommutator, Matrix.smul_mul, Matrix.mul_smul, smul_sub,
    smul_smul, mul_comm]

lemma scalar_I_sq (a : ℂ) : (Complex.I * a) * (Complex.I * a) = -(a ^ 2) := by
  rw [show (Complex.I * a) * (Complex.I * a) = (Complex.I * Complex.I) * a ^ 2 by ring]
  simp [Complex.I_mul_I]

/-- The nonabelian second-order contribution of two first-order edge increments
`i a A_mu` and `i a A_nu` is `-a^2 [A_mu,A_nu]`. -/
theorem matrixCommutator_I_smul (a : ℂ) (Aμ Aν : Matrix n n ℂ) :
    matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
      (-(a ^ 2)) • matrixCommutator Aμ Aν := by
  rw [matrixCommutator_smul]
  rw [scalar_I_sq]

omit [Fintype n] in
lemma two_zsmul_complex_smul (c : ℂ) (M : Matrix n n ℂ) :
    (2 : ℤ) • (c • M) = ((2 : ℂ) * c) • M := by
  simp [two_zsmul, add_smul, two_mul]

/-- Matrix form of the doubled formal second-order plaquette product coefficient.
The four formal first-order factors with increments `i a A_mu`, `i a A_nu`,
`-i a A_mu`, `-i a A_nu` contribute `-2 a^2 [A_mu,A_nu]` after doubling. -/
theorem doubledFormalSecondOrderProductCoefficient_matrix (a : ℂ)
    (Aμ Aν : Matrix n n ℂ) :
    doubledQuadraticSelfContribution ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) +
      (2 : ℤ) • orderedPairContribution ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
        (-2 * a ^ 2) • matrixCommutator Aμ Aν := by
  rw [doubledQuadraticPlaquetteContribution]
  change (2 : ℤ) • matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
    (-2 * a ^ 2) • matrixCommutator Aμ Aν
  rw [matrixCommutator_I_smul]
  rw [two_zsmul_complex_smul]
  rw [show ((2 : ℂ) * (-(a ^ 2))) = -2 * a ^ 2 by ring]

/-- The six commutators induced by the oriented first-order plaquette word
collapse to `-2 a^2 [A_mu,A_nu]`. -/
theorem firstOrderCommutatorSignSum_matrix (a : ℂ) (Aμ Aν : Matrix n n ℂ) :
    matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) +
      matrixCommutator ((Complex.I * a) • Aμ) (-((Complex.I * a) • Aμ)) +
      matrixCommutator ((Complex.I * a) • Aμ) (-((Complex.I * a) • Aν)) +
      matrixCommutator ((Complex.I * a) • Aν) (-((Complex.I * a) • Aμ)) +
      matrixCommutator ((Complex.I * a) • Aν) (-((Complex.I * a) • Aν)) +
      matrixCommutator (-((Complex.I * a) • Aμ)) (-((Complex.I * a) • Aν)) =
        (-2 * a ^ 2) • matrixCommutator Aμ Aν := by
  rw [show matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) +
      matrixCommutator ((Complex.I * a) • Aμ) (-((Complex.I * a) • Aμ)) +
      matrixCommutator ((Complex.I * a) • Aμ) (-((Complex.I * a) • Aν)) +
      matrixCommutator ((Complex.I * a) • Aν) (-((Complex.I * a) • Aμ)) +
      matrixCommutator ((Complex.I * a) • Aν) (-((Complex.I * a) • Aν)) +
      matrixCommutator (-((Complex.I * a) • Aμ)) (-((Complex.I * a) • Aν)) =
        (2 : ℤ) • matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) by
    exact fourIncrementCommutatorSignSum ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν)]
  rw [matrixCommutator_I_smul]
  rw [two_zsmul_complex_smul]
  rw [show ((2 : ℂ) * (-(a ^ 2))) = -2 * a ^ 2 by ring]

/-- First edge increment of a coordinate plaquette. -/
def plaquetteIncrement1 (a : ℂ) (Aμ : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I * a) • Aμ

/-- Second edge increment, including the transverse first derivative term. -/
def plaquetteIncrement2 (a : ℂ) (Aν dμAν : Matrix n n ℂ) : Matrix n n ℂ :=
  (Complex.I * a) • Aν + (Complex.I * a ^ 2) • dμAν

/-- Third edge increment, including the opposite transverse derivative term. -/
def plaquetteIncrement3 (a : ℂ) (Aμ dνAμ : Matrix n n ℂ) : Matrix n n ℂ :=
  -((Complex.I * a) • Aμ) - (Complex.I * a ^ 2) • dνAμ

/-- Fourth edge increment of a coordinate plaquette. -/
def plaquetteIncrement4 (a : ℂ) (Aν : Matrix n n ℂ) : Matrix n n ℂ :=
  -((Complex.I * a) • Aν)

omit [Fintype n] in
/-- The four oriented linear plaquette increments cancel to the exterior
finite-difference part `i a^2 (d_mu A_nu - d_nu A_mu)`. -/
theorem plaquetteLinearIncrementSum (a : ℂ)
    (Aμ Aν dμAν dνAμ : Matrix n n ℂ) :
    plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν =
        (Complex.I * a ^ 2) • (dμAν - dνAμ) := by
  simp [plaquetteIncrement1, plaquetteIncrement2, plaquetteIncrement3,
    plaquetteIncrement4, sub_eq_add_neg, smul_add]
  abel

/-- Algebraic finite-dimensional curvature core associated with two coordinate
directions. -/
def plaquetteCurvatureCore (Aμ Aν dμAν dνAμ : Matrix n n ℂ) : Matrix n n ℂ :=
  dμAν - dνAμ + Complex.I • matrixCommutator Aμ Aν

/-- Multiplying the curvature core by `i a^2` gives the linear exterior part plus
`-a^2 [A_mu,A_nu]`. -/
theorem plaquetteSecondOrderCurvatureCore (a : ℂ)
    (Aμ Aν dμAν dνAμ : Matrix n n ℂ) :
    (Complex.I * a ^ 2) • (dμAν - dνAμ) +
      (-(a ^ 2)) • matrixCommutator Aμ Aν =
        (Complex.I * a ^ 2) • plaquetteCurvatureCore Aμ Aν dμAν dνAμ := by
  unfold plaquetteCurvatureCore
  rw [smul_add]
  rw [smul_smul]
  rw [show (Complex.I * a ^ 2) * Complex.I = -a ^ 2 by
    rw [show (Complex.I * a ^ 2) * Complex.I = (Complex.I * Complex.I) * a ^ 2 by ring]
    simp [Complex.I_mul_I]]

/-- Combining the finite-difference linear part with the nonabelian second-order
commutator gives `i a^2` times the curvature core. -/
theorem plaquetteSecondOrderCore (a : ℂ)
    (Aμ Aν dμAν dνAμ : Matrix n n ℂ) :
    plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν +
      matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
        (Complex.I * a ^ 2) • plaquetteCurvatureCore Aμ Aν dμAν dνAμ := by
  rw [show plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν +
      matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
      (plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν) +
      matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) by abel]
  rw [plaquetteLinearIncrementSum]
  rw [matrixCommutator_I_smul]
  exact plaquetteSecondOrderCurvatureCore a Aμ Aν dμAν dνAμ

/-- Paper-facing finite matrix plaquette expansion: the finite-difference linear
part plus the nonabelian second-order commutator is `i a^2` times the curvature
core `d_mu A_nu - d_nu A_mu + i [A_mu,A_nu]`. -/
theorem finiteMatrixPlaquetteSecondOrderExpansion (a : ℂ)
    (Aμ Aν dμAν dνAμ : Matrix n n ℂ) :
    plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν +
      matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
        (Complex.I * a ^ 2) •
          (dμAν - dνAμ + Complex.I • matrixCommutator Aμ Aν) := by
  change
    plaquetteIncrement1 a Aμ + plaquetteIncrement2 a Aν dμAν +
      plaquetteIncrement3 a Aμ dνAμ + plaquetteIncrement4 a Aν +
      matrixCommutator ((Complex.I * a) • Aμ) ((Complex.I * a) • Aν) =
        (Complex.I * a ^ 2) • plaquetteCurvatureCore Aμ Aν dμAν dνAμ
  exact plaquetteSecondOrderCore a Aμ Aν dμAν dνAμ

end PlaquetteAlgebra

end NonabelianLift

end FiniteTransportComplex

end GaugeTransport
end Hardtest
