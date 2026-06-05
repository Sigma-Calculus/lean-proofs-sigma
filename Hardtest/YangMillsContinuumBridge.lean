/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.YangMills

/-!
# Yang--Mills continuum bridge

This module isolates the continuum assumptions used after the finite
Yang--Mills transport core.  The smooth representative connection, controlled
plaquette expansion, and leading local effective-field-theory classification
are recorded as explicit hypotheses, not as global Lean axioms.

The main theorem proves that the already formalized finite transport core,
together with these three bridge hypotheses, yields the paper-facing conditional
Yang--Mills leading-term conclusion.
-/

namespace Hardtest
namespace YangMills
namespace ContinuumBridge

open scoped BigOperators
open GaugeTransport
open GaugeTransport.FiniteTransportComplex
open GaugeTransport.FiniteTransportComplex.NonabelianLift

variable {V E F G X : Type*}
variable [Fintype E] [Fintype F]
variable [Group G]
variable {Patch Connection Curvature LocalDensity : Type*}

/-! ## Continuum bridge hypotheses -/

/-- A smooth representative completion of finite non-abelian transport.

The fields are deliberately hypotheses: they name the continuum data and the
two semantic links needed by the Yang--Mills paper, namely that finite holonomy
is represented by a smooth connection and that the finite plaquette core is
represented by its curvature. -/
structure SmoothRepresentativeCompletion
    (K : FiniteTransportComplex V E F) (rho : E → G)
    (Patch Connection Curvature : Type*) where
  patch : Patch
  connection : Connection
  curvature : Curvature
  hasSmoothRepresentative : Prop
  finiteHolonomyRepresented : Prop
  curvatureRepresentsPlaquetteCore : Prop

/-- Controlled path-ordered plaquette expansion for a smooth representative
completion.

This is the analytic bridge layer: the leading finite plaquette term is
identified with the curvature density once the representative connection,
plaquette-core identification, and remainder control hypotheses are supplied. -/
structure PathOrderedPlaquetteExpansion
    {K : FiniteTransportComplex V E F} {rho : E → G}
    (completion : SmoothRepresentativeCompletion K rho Patch Connection Curvature)
    (LocalDensity : Type*) where
  leadingTerm : LocalDensity
  curvatureDensity : LocalDensity
  remainderControlled : Prop
  leadingTerm_eq_curvatureDensity :
    completion.hasSmoothRepresentative →
      completion.curvatureRepresentsPlaquetteCore →
        remainderControlled →
          leadingTerm = curvatureDensity

/-- Leading local effective-field-theory classifier for the admissible
parity-even gauge-invariant density. -/
structure LeadingEFTClassifier (LocalDensity : Type*) where
  yangMillsDensity : LocalDensity
  admissibleLeadingTerm : LocalDensity → Prop
  sound :
    ∀ term : LocalDensity,
      admissibleLeadingTerm term →
        term = yangMillsDensity

/-! ## Conditional Yang--Mills bridge theorem -/

omit [Group G] in
/-- The continuum bridge theorem: if the finite transport core admits a smooth
representative completion, the path-ordered plaquette expansion has controlled
remainder, and the resulting curvature density is admissible for the leading
local classifier, then the leading term is the Yang--Mills density. -/
theorem conditionalYangMillsLeadingTerm
    {K : FiniteTransportComplex V E F} {rho : E → G}
    (completion : SmoothRepresentativeCompletion K rho Patch Connection Curvature)
    (expansion : PathOrderedPlaquetteExpansion completion LocalDensity)
    (classifier : LeadingEFTClassifier LocalDensity)
    (hSmooth : completion.hasSmoothRepresentative)
    (hCurvature : completion.curvatureRepresentsPlaquetteCore)
    (hRemainder : expansion.remainderControlled)
    (hAdmissible : classifier.admissibleLeadingTerm expansion.curvatureDensity) :
    expansion.leadingTerm = classifier.yangMillsDensity := by
  calc
    expansion.leadingTerm = expansion.curvatureDensity :=
      expansion.leadingTerm_eq_curvatureDensity hSmooth hCurvature hRemainder
    _ = classifier.yangMillsDensity :=
      classifier.sound expansion.curvatureDensity hAdmissible

/-! ## Finite core plus continuum bridge -/

noncomputable section MatrixBridge

variable {n : Type*} [Fintype n]

/-- Bundled paper-facing bridge statement: the already formalized finite
Yang--Mills transport core and the explicit continuum bridge hypotheses imply
the conditional leading Yang--Mills density conclusion. -/
theorem finiteCoreAndConditionalYangMillsLeadingTerm
    (K : FiniteTransportComplex V E F)
    (Lambda : ℝ) (sigma : E → ℝ) (lambda : V → ℝ)
    (e : E) (c : E → ℤ) (hclosedChain : K.IsClosed1Chain c) (S : F → ℤ)
    (chi : G → X) (hchi : IsClassFunction chi)
    (rho : E → G) (g : V → G) (base : V) (edges : List E)
    (hclosedLoop : NonabelianLift.IsClosedEdgeLoop K base edges)
    (Gamma : CubeEdgeHolonomies.CubeVertexFrames G) (C : CubeEdgeHolonomies G)
    (a : ℂ) (A_mu A_nu d_mu_A_nu d_nu_A_mu : Matrix n n ℂ)
    (completion : SmoothRepresentativeCompletion K rho Patch Connection Curvature)
    (expansion : PathOrderedPlaquetteExpansion completion LocalDensity)
    (classifier : LeadingEFTClassifier LocalDensity)
    (hSmooth : completion.hasSmoothRepresentative)
    (hCurvature : completion.curvatureRepresentsPlaquetteCore)
    (hRemainder : expansion.remainderControlled)
    (hAdmissible : classifier.admissibleLeadingTerm expansion.curvatureDensity) :
    (phase Lambda (K.exactShift sigma lambda e) =
        phase Lambda (-(lambda (K.source e))) *
          phase Lambda (sigma e) *
            phase Lambda (lambda (K.target e)) ∧
      chainHolonomy Lambda (K.exactShift sigma lambda) c =
        chainHolonomy Lambda sigma c ∧
      chainHolonomy Lambda sigma (K.boundary2 S) =
        K.faceHolonomy Lambda sigma S) ∧
    (edgeListHolonomy (frameChange K rho g) edges =
        (g base)⁻¹ * edgeListHolonomy rho edges * g base ∧
      chi (edgeListHolonomy (frameChange K rho g) edges) =
        chi (edgeListHolonomy rho edges)) ∧
    ((CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod = 1 ∧
      (CubeEdgeHolonomies.basedFaceHolonomyProducts
          (CubeEdgeHolonomies.frameChange Gamma C)).prod = 1 ∧
      chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts
          (CubeEdgeHolonomies.frameChange Gamma C)).prod) =
        chi ((CubeEdgeHolonomies.basedFaceHolonomyProducts C).prod)) ∧
    (plaquetteIncrement1 a A_mu + plaquetteIncrement2 a A_nu d_mu_A_nu +
      plaquetteIncrement3 a A_mu d_nu_A_mu + plaquetteIncrement4 a A_nu +
      matrixCommutator ((Complex.I * a) • A_mu) ((Complex.I * a) • A_nu) =
        (Complex.I * a ^ 2) •
          (d_mu_A_nu - d_nu_A_mu + Complex.I • matrixCommutator A_mu A_nu)) ∧
    expansion.leadingTerm = classifier.yangMillsDensity := by
  exact ⟨
    finiteYangMillsAbelianTransportCore K Lambda sigma lambda e c hclosedChain S,
    finiteYangMillsClosedLoopGaugeInvariantCore K chi hchi rho g base edges hclosedLoop,
    finiteYangMillsCubeBianchiCore chi hchi Gamma C,
    finiteYangMillsMatrixPlaquetteCurvatureCore a A_mu A_nu d_mu_A_nu d_nu_A_mu,
    conditionalYangMillsLeadingTerm
      completion expansion classifier hSmooth hCurvature hRemainder hAdmissible⟩

end MatrixBridge

end ContinuumBridge
end YangMills
end Hardtest
