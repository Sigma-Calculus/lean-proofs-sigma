/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.GaugeTransport

/-!
# Yang--Mills finite transport formalization

This module provides paper-facing Lean names for the finite theorem-level
transport core used by the Yang--Mills universality paper. It deliberately
stays at the finite holonomy level: exact-shift abelian transport, closed-loop
frame covariance, class-function invariance, finite cube/Bianchi identities,
and the algebraic matrix plaquette curvature core.

The local continuum completion, path-ordered exponential analysis, BCH
remainder estimates, and effective-field-theory operator classification are not
part of this finite module.
-/

namespace Hardtest
namespace YangMills

open scoped BigOperators
open GaugeTransport
open GaugeTransport.FiniteTransportComplex
open GaugeTransport.FiniteTransportComplex.NonabelianLift

variable {V E F G X : Type*}
variable [Fintype E] [Fintype F]
variable [Group G]

/-! ## Abelian sigma transport core -/

/-- Yang--Mills-paper-facing endpoint phase law for exact shifts of abelian
sigma link transport. -/
theorem finiteYangMillsExactShiftEndpointPhaseAction
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (e : E) :
    phase Lambda (K.exactShift sigma lambda e) =
      phase Lambda (-(lambda (K.source e))) *
        phase Lambda (sigma e) *
          phase Lambda (lambda (K.target e)) :=
  finiteExactShiftEndpointPhaseAction K Lambda sigma lambda e

/-- Yang--Mills-paper-facing exact-shift invariance of abelian closed-chain
holonomy. -/
theorem finiteYangMillsClosedChainHolonomyExactShiftInvariant
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ) (c : E → ℤ)
    (hclosed : K.IsClosed1Chain c) :
    chainHolonomy Lambda (K.exactShift sigma lambda) c =
      chainHolonomy Lambda sigma c :=
  finiteClosedChainHolonomyExactShiftInvariant K Lambda sigma lambda c hclosed

/-- Yang--Mills-paper-facing exact discrete Stokes law for abelian face
holonomy. -/
theorem finiteYangMillsDiscreteStokesHolonomy
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (S : F → ℤ) :
    chainHolonomy Lambda sigma (K.boundary2 S) =
      K.faceHolonomy Lambda sigma S :=
  finiteDiscreteStokesHolonomy K Lambda sigma S

/-- Yang--Mills-paper-facing existence of a reduced representative in every
finite exact-shift class. -/
theorem finiteYangMillsReducedRepresentativeExists
    (K : FiniteTransportComplex V E F) (sigma : E → ℝ) :
    ∃ R : K.ReducedRepresentative sigma,
      K.IsReducedEnergyMinimizer sigma R.lambda :=
  finiteReducedRepresentativeExists K sigma

/-- Bundled finite abelian transport core: endpoint phase covariance, closed
holonomy exact-shift invariance, and exact face-curvature Stokes holonomy. -/
theorem finiteYangMillsAbelianTransportCore
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ)
    (e : E) (c : E → ℤ) (hclosed : K.IsClosed1Chain c) (S : F → ℤ) :
    phase Lambda (K.exactShift sigma lambda e) =
        phase Lambda (-(lambda (K.source e))) *
          phase Lambda (sigma e) *
            phase Lambda (lambda (K.target e)) ∧
      chainHolonomy Lambda (K.exactShift sigma lambda) c =
        chainHolonomy Lambda sigma c ∧
      chainHolonomy Lambda sigma (K.boundary2 S) =
        K.faceHolonomy Lambda sigma S := by
  exact ⟨finiteYangMillsExactShiftEndpointPhaseAction K Lambda sigma lambda e,
    finiteYangMillsClosedChainHolonomyExactShiftInvariant K Lambda sigma lambda c hclosed,
    finiteYangMillsDiscreteStokesHolonomy K Lambda sigma S⟩

/-! ## Nonabelian finite lift and frame invariance -/

/-- Yang--Mills-paper-facing frame covariance of a finite closed non-abelian
edge-loop holonomy. -/
theorem finiteYangMillsClosedLoopFrameConjugation
    (K : FiniteTransportComplex V E F)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : NonabelianLift.IsClosedEdgeLoop K base edges) :
    edgeListHolonomy (frameChange K rho g) edges =
      (g base)⁻¹ * edgeListHolonomy rho edges * g base :=
  finiteNonabelianClosedEdgeLoopFrameConjugation K rho g base edges hclosed

/-- Yang--Mills-paper-facing gauge invariance of finite closed-loop class
functions. -/
theorem finiteYangMillsClosedLoopClassFunctionInvariant
    (K : FiniteTransportComplex V E F)
    (chi : G → X) (hchi : IsClassFunction chi)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : NonabelianLift.IsClosedEdgeLoop K base edges) :
    chi (edgeListHolonomy (frameChange K rho g) edges) =
      chi (edgeListHolonomy rho edges) :=
  finiteNonabelianClosedEdgeLoopClassFunctionInvariant K chi hchi rho g base edges hclosed

/-- Bundled finite non-abelian closed-loop transport core: frame covariance and
class-function invariance. -/
theorem finiteYangMillsClosedLoopGaugeInvariantCore
    (K : FiniteTransportComplex V E F)
    (chi : G → X) (hchi : IsClassFunction chi)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosed : NonabelianLift.IsClosedEdgeLoop K base edges) :
    edgeListHolonomy (frameChange K rho g) edges =
        (g base)⁻¹ * edgeListHolonomy rho edges * g base ∧
      chi (edgeListHolonomy (frameChange K rho g) edges) =
        chi (edgeListHolonomy rho edges) := by
  exact ⟨finiteYangMillsClosedLoopFrameConjugation K rho g base edges hclosed,
    finiteYangMillsClosedLoopClassFunctionInvariant K chi hchi rho g base edges hclosed⟩

/-! ## Finite cube/Bianchi core -/

/-- Yang--Mills-paper-facing finite cube/Bianchi identity: the ordered product of
six based face holonomies evaluates to the identity. -/
theorem finiteYangMillsCubeBianchiProductIdentity
    (C : CubeEdgeHolonomies G) :
    (CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod = 1 :=
  CubeEdgeHolonomies.finiteCubeBasedFaceHolonomyProductIdentity C

/-- Yang--Mills-paper-facing frame covariance of the finite cube/Bianchi face
holonomy product. -/
theorem finiteYangMillsCubeBianchiFrameChangeConjugation
    (Gamma : CubeEdgeHolonomies.CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (CubeEdgeHolonomies.basedFaceHolonomyProducts
        (CubeEdgeHolonomies.frameChange Gamma C)).prod =
      Gamma.v000⁻¹ * (CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod *
        Gamma.v000 :=
  CubeEdgeHolonomies.finiteCubeBasedFaceHolonomyProductFrameChangeConjugation Gamma C

/-- Yang--Mills-paper-facing class-function invariance of the cube/Bianchi face
holonomy product under vertex frame changes. -/
theorem finiteYangMillsCubeBianchiClassFunctionInvariant
    (chi : G → X) (hchi : IsClassFunction chi)
    (Gamma : CubeEdgeHolonomies.CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts
        (CubeEdgeHolonomies.frameChange Gamma C)).prod) =
      chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod) :=
  CubeEdgeHolonomies.finiteCubeBasedFaceHolonomyProductClassFunctionInvariant
    chi hchi Gamma C

/-- Yang--Mills-paper-facing frame-stability of the finite cube/Bianchi identity. -/
theorem finiteYangMillsCubeBianchiFrameChangeIdentity
    (Gamma : CubeEdgeHolonomies.CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (CubeEdgeHolonomies.basedFaceHolonomyProducts
        (CubeEdgeHolonomies.frameChange Gamma C)).prod = 1 :=
  CubeEdgeHolonomies.finiteCubeBasedFaceHolonomyProductFrameChangeIdentity Gamma C

/-- Yang--Mills-paper-facing observable evaluation of the cube/Bianchi product at
the group identity. -/
theorem finiteYangMillsCubeBianchiObservableAtIdentity
    (chi : G → X) (C : CubeEdgeHolonomies G) :
    chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod) = chi 1 :=
  CubeEdgeHolonomies.finiteCubeBasedFaceHolonomyProductObservableAtIdentity chi C

/-- Bundled finite cube/Bianchi core: product identity, frame-stability, and
class-function invariance. -/
theorem finiteYangMillsCubeBianchiCore
    (chi : G → X) (hchi : IsClassFunction chi)
    (Gamma : CubeEdgeHolonomies.CubeVertexFrames G) (C : CubeEdgeHolonomies G) :
    (CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod = 1 ∧
      (CubeEdgeHolonomies.basedFaceHolonomyProducts
          (CubeEdgeHolonomies.frameChange Gamma C)).prod = 1 ∧
      chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts
          (CubeEdgeHolonomies.frameChange Gamma C)).prod) =
        chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod) := by
  exact ⟨finiteYangMillsCubeBianchiProductIdentity C,
    finiteYangMillsCubeBianchiFrameChangeIdentity Gamma C,
    finiteYangMillsCubeBianchiClassFunctionInvariant chi hchi Gamma C⟩

/-! ## Algebraic matrix plaquette curvature core -/

noncomputable section PlaquetteCore

variable {n : Type*} [Fintype n]

omit [Fintype n] in
/-- Yang--Mills-paper-facing linear exterior part of the coordinate plaquette
increments. -/
theorem finiteYangMillsPlaquetteLinearExteriorPart
    (a : ℂ) (A_mu A_nu d_mu_A_nu d_nu_A_mu : Matrix n n ℂ) :
    plaquetteIncrement1 a A_mu + plaquetteIncrement2 a A_nu d_mu_A_nu +
      plaquetteIncrement3 a A_mu d_nu_A_mu + plaquetteIncrement4 a A_nu =
        (Complex.I * a ^ 2) • (d_mu_A_nu - d_nu_A_mu) :=
  plaquetteLinearIncrementSum a A_mu A_nu d_mu_A_nu d_nu_A_mu

/-- Yang--Mills-paper-facing nonabelian first-order commutator contribution of
the plaquette word. -/
theorem finiteYangMillsPlaquetteCommutatorContribution
    (a : ℂ) (A_mu A_nu : Matrix n n ℂ) :
    matrixCommutator ((Complex.I * a) • A_mu) ((Complex.I * a) • A_nu) =
      (-(a ^ 2)) • matrixCommutator A_mu A_nu :=
  matrixCommutator_I_smul a A_mu A_nu

/-- Yang--Mills-paper-facing finite matrix plaquette expansion core: the
finite-difference exterior part plus the nonabelian second-order commutator is
`i a^2` times the curvature core. -/
theorem finiteYangMillsMatrixPlaquetteCurvatureCore
    (a : ℂ) (A_mu A_nu d_mu_A_nu d_nu_A_mu : Matrix n n ℂ) :
    plaquetteIncrement1 a A_mu + plaquetteIncrement2 a A_nu d_mu_A_nu +
      plaquetteIncrement3 a A_mu d_nu_A_mu + plaquetteIncrement4 a A_nu +
      matrixCommutator ((Complex.I * a) • A_mu) ((Complex.I * a) • A_nu) =
        (Complex.I * a ^ 2) •
          (d_mu_A_nu - d_nu_A_mu + Complex.I • matrixCommutator A_mu A_nu) :=
  finiteMatrixPlaquetteSecondOrderExpansion a A_mu A_nu d_mu_A_nu d_nu_A_mu

end PlaquetteCore

end YangMills
end Hardtest
