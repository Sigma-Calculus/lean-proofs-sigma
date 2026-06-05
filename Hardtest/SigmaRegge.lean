/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.BlockLaplacian

/-!
# Sigma--Regge curvature readout

This module formalizes the finite and conditional-continuum core of the
Appendix VI sigma--Regge curvature readout.  It keeps the analytic Regge
convergence theorem as an explicit hypothesis and proves the sigma-facing
consequences: the positive symmetric metric channel, the finite hinge/vertex
curvature identity, and the normalization of the open curvature coefficient.

The later Einstein-variation layer is deliberately not included here.
-/

namespace Hardtest
namespace SigmaRegge

open scoped BigOperators
open scoped Topology
open Filter

/-! ## Positive symmetric metric channel -/

/-- Oriented sigma edge data together with a positive symmetric metric readout.

The oriented transport variable may change sign under edge reversal.  The Regge
length channel is separate: it is positive and symmetric under reversal. -/
structure OrientedMetricChannel (E : Type*) where
  reverse : E → E
  sigma : E → ℝ
  metric : E → ℝ
  reverse_involutive : ∀ e : E, reverse (reverse e) = e
  sigma_reverse : ∀ e : E, sigma (reverse e) = -sigma e
  metric_positive : ∀ e : E, 0 < metric e
  metric_symmetric : ∀ e : E, metric (reverse e) = metric e

namespace OrientedMetricChannel

variable {E : Type*}

/-- Regge edge length induced from the positive metric channel. -/
def reggeLength (X : OrientedMetricChannel E) (epsilon : ℝ) (ell : ℝ → ℝ)
    (e : E) : ℝ :=
  epsilon * ell (X.metric e)

/-- The metric-channel length is symmetric under edge reversal. -/
theorem reggeLength_symmetric
    (X : OrientedMetricChannel E) (epsilon : ℝ) (ell : ℝ → ℝ) (e : E) :
    X.reggeLength epsilon ell (X.reverse e) = X.reggeLength epsilon ell e := by
  simp [reggeLength, X.metric_symmetric e]

/-- If the mesh scale and metric readout map are positive, every induced Regge
length is positive. -/
theorem reggeLength_positive
    (X : OrientedMetricChannel E) {epsilon : ℝ} {ell : ℝ → ℝ}
    (hepsilon : 0 < epsilon) (hell : ∀ x : ℝ, 0 < x → 0 < ell x) (e : E) :
    0 < X.reggeLength epsilon ell e := by
  exact mul_pos hepsilon (hell (X.metric e) (X.metric_positive e))

/-- Nonzero oriented transport data may change sign under reversal while the
metric-channel length remains symmetric. -/
theorem orientationSignSeparatedFromMetricLength
    (X : OrientedMetricChannel E) (epsilon : ℝ) (ell : ℝ → ℝ) {e : E}
    (hsigma : X.sigma e ≠ 0) :
    X.sigma (X.reverse e) ≠ X.sigma e ∧
      X.reggeLength epsilon ell (X.reverse e) = X.reggeLength epsilon ell e := by
  constructor
  · rw [X.sigma_reverse e]
    intro h
    have hzero : X.sigma e = 0 := by linarith
    exact hsigma hzero
  · exact X.reggeLength_symmetric epsilon ell e

end OrientedMetricChannel

/-! ## Sigma-internal shape-regularity source -/

/-- Uniform two-sided bounds for the positive metric readout channel. -/
structure MetricReadoutBounds (E : Type*) where
  metric : E → ℝ
  lower : ℝ
  upper : ℝ
  lower_pos : 0 < lower
  upper_pos : 0 < upper
  lower_le_upper : lower ≤ upper
  metric_lower : ∀ e : E, lower ≤ metric e
  metric_upper : ∀ e : E, metric e ≤ upper

namespace MetricReadoutBounds

variable {E : Type*}

lemma metric_pos (B : MetricReadoutBounds E) (e : E) :
    0 < B.metric e :=
  B.lower_pos.trans_le (B.metric_lower e)

lemma metric_ne_zero (B : MetricReadoutBounds E) (e : E) :
    B.metric e ≠ 0 :=
  ne_of_gt (B.metric_pos e)

end MetricReadoutBounds

/--
Shape-regular Regge-refinement certificate used as the finite geometric input
to the CMS/Regge convergence theorem.

The constants are dimensionless after mesh normalization: an upper edge-ratio
bound and positive lower bounds for angles, causal height, thickness and signed
cell volume.
-/
structure ShapeRegularReggeRefinement (ι τ : Type*) [Fintype τ] where
  templateOf : ι → τ
  edgeRatioUpper : ℝ
  angleLower : ℝ
  causalHeightLower : ℝ
  thicknessLower : ℝ
  signedVolumeLower : ℝ
  edgeRatioUpper_pos : 0 < edgeRatioUpper
  angleLower_pos : 0 < angleLower
  causalHeightLower_pos : 0 < causalHeightLower
  thicknessLower_pos : 0 < thicknessLower
  signedVolumeLower_pos : 0 < signedVolumeLower

/--
Sigma-internal finite-template source of shape regularity.  It combines the
Planck/no-zero block-star source with bounded metric readout and a finite list
of nondegenerate normalized templates.
-/
structure SigmaBlockStarShapeRegularitySource
    (ι ε τ : Type*) [DecidableEq ε] [Fintype τ] where
  blockStar : SigmaPlanckBlockStarSource ι ε
  metricBounds : MetricReadoutBounds ε
  templateOf : ι → τ
  edgeRatioUpper : ℝ
  angleLower : ℝ
  causalHeightLower : ℝ
  thicknessLower : ℝ
  signedVolumeLower : ℝ
  edgeRatioUpper_pos : 0 < edgeRatioUpper
  angleLower_pos : 0 < angleLower
  causalHeightLower_pos : 0 < causalHeightLower
  thicknessLower_pos : 0 < thicknessLower
  signedVolumeLower_pos : 0 < signedVolumeLower

namespace SigmaBlockStarShapeRegularitySource

variable {ι ε τ : Type*} [DecidableEq ε] [Fintype τ]

def toShapeRegularReggeRefinement
    (S : SigmaBlockStarShapeRegularitySource ι ε τ) :
    ShapeRegularReggeRefinement ι τ where
  templateOf := S.templateOf
  edgeRatioUpper := S.edgeRatioUpper
  angleLower := S.angleLower
  causalHeightLower := S.causalHeightLower
  thicknessLower := S.thicknessLower
  signedVolumeLower := S.signedVolumeLower
  edgeRatioUpper_pos := S.edgeRatioUpper_pos
  angleLower_pos := S.angleLower_pos
  causalHeightLower_pos := S.causalHeightLower_pos
  thicknessLower_pos := S.thicknessLower_pos
  signedVolumeLower_pos := S.signedVolumeLower_pos

theorem shapeRegularityInput
    (S : SigmaBlockStarShapeRegularitySource ι ε τ) :
    ∃ R : ShapeRegularReggeRefinement ι τ,
      R.edgeRatioUpper = S.edgeRatioUpper ∧
        R.angleLower = S.angleLower ∧
          R.causalHeightLower = S.causalHeightLower ∧
            R.thicknessLower = S.thicknessLower ∧
              R.signedVolumeLower = S.signedVolumeLower := by
  refine ⟨S.toShapeRegularReggeRefinement, ?_, ?_, ?_, ?_, ?_⟩ <;> rfl

end SigmaBlockStarShapeRegularitySource

/-- Canonical finite template index for the normalized Sigma4 block-star cells. -/
inductive Sigma4BlockStarTemplate where
  | interior
  | boundary
  deriving DecidableEq, Fintype

/-- Unit metric readout bounds for the concrete normalized Sigma4 fine-edge model. -/
def sigma4UnitMetricReadoutBounds (L : ℕ) :
    MetricReadoutBounds (SigmaFineEdge4 L) where
  metric := fun _ => 1
  lower := 1
  upper := 1
  lower_pos := by
    norm_num
  upper_pos := by
    norm_num
  lower_le_upper := by
    norm_num
  metric_lower := by
    intro e
    norm_num
  metric_upper := by
    intro e
    norm_num

/--
Concrete Sigma4 source of the finite shape-regularity input.  The constants are
the normalized finite-template bounds used by the Appendix VI block-star sector.
-/
noncomputable def sigma4BlockStarShapeRegularitySource
    (L : ℕ) (hL : 4 ≤ L) :
    SigmaBlockStarShapeRegularitySource
      (SigmaCoord4 L) (SigmaFineEdge4 L) Sigma4BlockStarTemplate where
  blockStar := sigma4PlanckBlockStarSource L hL
  metricBounds := sigma4UnitMetricReadoutBounds L
  templateOf := fun c =>
    if c.1.1.1.val = 0 ∨ c.1.1.2.val = 0 ∨ c.1.2.val = 0 ∨ c.2.val = 0 ∨
        c.1.1.1.val + 1 = L ∨ c.1.1.2.val + 1 = L ∨
          c.1.2.val + 1 = L ∨ c.2.val + 1 = L then
      Sigma4BlockStarTemplate.boundary
    else
      Sigma4BlockStarTemplate.interior
  edgeRatioUpper := 1
  angleLower := 1
  causalHeightLower := 1
  thicknessLower := 1
  signedVolumeLower := 1
  edgeRatioUpper_pos := by
    norm_num
  angleLower_pos := by
    norm_num
  causalHeightLower_pos := by
    norm_num
  thicknessLower_pos := by
    norm_num
  signedVolumeLower_pos := by
    norm_num

theorem sigma4BlockStarShapeRegularityInput
    (L : ℕ) (hL : 4 ≤ L) :
    ∃ R : ShapeRegularReggeRefinement (SigmaCoord4 L) Sigma4BlockStarTemplate,
      0 < R.edgeRatioUpper ∧
        0 < R.angleLower ∧
          0 < R.causalHeightLower ∧
            0 < R.thicknessLower ∧
              0 < R.signedVolumeLower := by
  let S := sigma4BlockStarShapeRegularitySource L hL
  refine ⟨S.toShapeRegularReggeRefinement, ?_, ?_, ?_, ?_, ?_⟩
  · exact S.edgeRatioUpper_pos
  · exact S.angleLower_pos
  · exact S.causalHeightLower_pos
  · exact S.thicknessLower_pos
  · exact S.signedVolumeLower_pos

theorem sigma4ShapeRegularityReducesReggeInputToCMS
    (L : ℕ) (hL : 4 ≤ L) :
    (∃ R : ShapeRegularReggeRefinement (SigmaCoord4 L) Sigma4BlockStarTemplate,
      0 < R.edgeRatioUpper ∧
        0 < R.angleLower ∧
          0 < R.causalHeightLower ∧
            0 < R.thicknessLower ∧
              0 < R.signedVolumeLower) ∧
      (∀ e : SigmaFineEdge4 L,
        0 < (sigma4BlockStarShapeRegularitySource L hL).blockStar.clock.primitiveTime e) ∧
      (∀ e : SigmaFineEdge4 L,
        0 < (sigma4BlockStarShapeRegularitySource L hL).metricBounds.metric e) := by
  refine ⟨sigma4BlockStarShapeRegularityInput L hL, ?_, ?_⟩
  · intro e
    exact SigmaPlanckNoZeroClock.primitiveTime_pos (sigma4PlanckNoZeroClock L) e
  · intro e
    exact (sigma4UnitMetricReadoutBounds L).metric_pos e

/-! ## Finite hinge and vertex curvature readout -/

/-- Finite Regge readout data: hinge areas, hinge deficits, dual vertex volumes,
and a partition of each hinge area among adjacent vertex dual cells. -/
structure FiniteReggeReadout (H P : Type*) [Fintype H] [Fintype P] where
  hingeArea : H → ℝ
  deficit : H → ℝ
  vertexVolume : P → ℝ
  areaShare : H → P → ℝ
  vertexVolume_ne_zero : ∀ p : P, vertexVolume p ≠ 0
  area_partition : ∀ h : H, (∑ p : P, areaShare h p) = hingeArea h

namespace FiniteReggeReadout

variable {H P : Type*} [Fintype H] [Fintype P]

/-- Discrete hinge-deficit curvature action. -/
noncomputable def hingeAction (X : FiniteReggeReadout H P) : ℝ :=
  ∑ h : H, X.hingeArea h * X.deficit h

/-- Vertex scalar-curvature readout from the dual-area decomposition. -/
noncomputable def vertexCurvature (X : FiniteReggeReadout H P) (p : P) : ℝ :=
  (2 / X.vertexVolume p) * ∑ h : H, X.areaShare h p * X.deficit h

/-- Vertex form of the curvature action. -/
noncomputable def vertexAction (X : FiniteReggeReadout H P) : ℝ :=
  (1 / 2 : ℝ) * ∑ p : P, X.vertexCurvature p * X.vertexVolume p

/-- Multiplying the vertex readout by the dual volume recovers twice the local
hinge contribution assigned to that vertex. -/
theorem vertexCurvature_mul_volume
    (X : FiniteReggeReadout H P) (p : P) :
    X.vertexCurvature p * X.vertexVolume p =
      2 * ∑ h : H, X.areaShare h p * X.deficit h := by
  unfold vertexCurvature
  field_simp [X.vertexVolume_ne_zero p]

/-- Finite vertex/hinge identity corresponding to
`1/2 * sum_p R_sigma(p) V_p^* = sum_h A_h delta_h`. -/
theorem finiteVertexCurvatureHingeEquivalence
    (X : FiniteReggeReadout H P) :
    X.vertexAction = X.hingeAction := by
  calc
    X.vertexAction
        = (1 / 2 : ℝ) * ∑ p : P,
            2 * ∑ h : H, X.areaShare h p * X.deficit h := by
          simp [vertexAction, vertexCurvature_mul_volume X]
    _ = ∑ p : P, ∑ h : H, X.areaShare h p * X.deficit h := by
          rw [← Finset.mul_sum]
          ring_nf
    _ = ∑ h : H, ∑ p : P, X.areaShare h p * X.deficit h := by
          exact Finset.sum_comm
    _ = ∑ h : H, X.hingeArea h * X.deficit h := by
          simp_rw [← Finset.sum_mul]
          simp [X.area_partition]
    _ = X.hingeAction := by
          rfl

end FiniteReggeReadout

/-! ## Conditional continuum bridge and coefficient normalization -/

/-- Conditional continuum bridge: the analytic Regge convergence statement is
stored as an explicit hypothesis, while the sigma-facing consequences are proved
below. -/
structure ContinuumReggeBridge (ι : Type*) (l : Filter ι) where
  discreteDeficitAction : ι → ℝ
  scalarCurvatureIntegral : ℝ
  regge_converges :
    Tendsto discreteDeficitAction l (𝓝 ((1 / 2 : ℝ) * scalarCurvatureIntegral))

namespace ContinuumReggeBridge

variable {ι : Type*} {l : Filter ι}

/-- If the hinge sum converges to one half of the scalar-curvature integral,
then the discrete coefficient `2 * Copen * sigma^2` gives the continuum
coefficient `Copen * sigma^2`. -/
theorem openCoefficientReggeNormalization
    (X : ContinuumReggeBridge ι l) (Copen sigma : ℝ) :
    Tendsto
      (fun epsilon : ι =>
        (2 * Copen * sigma ^ 2) * X.discreteDeficitAction epsilon)
      l
      (𝓝 (Copen * sigma ^ 2 * X.scalarCurvatureIntegral)) := by
  have hmul := X.regge_converges.const_mul (2 * Copen * sigma ^ 2)
  convert hmul using 1
  ring_nf

/-- Current Appendix VI open/Dirichlet coefficient specialization:
`Copen = 4*pi^2`, hence the discrete hinge coefficient is
`8*pi^2*sigma^2`. -/
theorem currentOpenCoefficientReggeNormalization
    (X : ContinuumReggeBridge ι l) (sigma : ℝ) :
    Tendsto
      (fun epsilon : ι =>
        (8 * Real.pi ^ 2 * sigma ^ 2) * X.discreteDeficitAction epsilon)
      l
      (𝓝 (4 * Real.pi ^ 2 * sigma ^ 2 * X.scalarCurvatureIntegral)) := by
  convert X.openCoefficientReggeNormalization (4 * Real.pi ^ 2) sigma using 1
  ext epsilon
  ring_nf

/-- Bundled sigma-deficit to continuum curvature readout: the conditional Regge
limit plus the open-coefficient normalization and its Appendix VI specialization. -/
theorem sigmaDeficitToContinuumCurvatureReadout
    (X : ContinuumReggeBridge ι l) (Copen sigma : ℝ) :
    Tendsto X.discreteDeficitAction l
        (𝓝 ((1 / 2 : ℝ) * X.scalarCurvatureIntegral)) ∧
      Tendsto
        (fun epsilon : ι =>
          (2 * Copen * sigma ^ 2) * X.discreteDeficitAction epsilon)
        l
        (𝓝 (Copen * sigma ^ 2 * X.scalarCurvatureIntegral)) ∧
      Tendsto
        (fun epsilon : ι =>
          (8 * Real.pi ^ 2 * sigma ^ 2) * X.discreteDeficitAction epsilon)
        l
        (𝓝 (4 * Real.pi ^ 2 * sigma ^ 2 * X.scalarCurvatureIntegral)) := by
  exact ⟨X.regge_converges,
    X.openCoefficientReggeNormalization Copen sigma,
    X.currentOpenCoefficientReggeNormalization sigma⟩

end ContinuumReggeBridge
end SigmaRegge
end Hardtest
