/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.HorizonReadout

/-!
# Sigma patch visibility thresholds

This file formalizes the finite core of the Sigma patch visibility bridge:
positive Planck-clock patch support, representative/readout stability, finite
collapse action, and the external visibility threshold
`exp (-A) <= epsilon` iff `log epsilon⁻¹ <= A`.

The file deliberately does not formalize continuum semigroups, thermodynamic
Hawking readouts, or horizon-to-radiation reconstruction.  Those analytic and
physical layers are TeX-level inputs built on top of this finite theorem-level
core.
-/

namespace SigmaProofs.PatchVisibility

noncomputable section

/-- Finite Sigma patch with positive Planck-clock counts and positive weights. -/
structure FiniteSigmaPatch (Edge : Type*) [Fintype Edge] where
  nonempty_edges : Nonempty Edge
  clockCount : Edge → ℕ
  clockCount_pos : ∀ e, 1 ≤ clockCount e
  weight : Edge → ℝ
  weight_pos : ∀ e, 0 < weight e
  deltaSigma : Edge → ℝ

namespace FiniteSigmaPatch

variable {Edge : Type*} [Fintype Edge] (P : FiniteSigmaPatch Edge)

/-- Dimensionless patch time in Planck units. -/
def dimensionlessTime : ℕ :=
  Finset.univ.sum P.clockCount

/-- Patch time obtained by multiplying the dimensionless count by a Planck time. -/
def patchTime (planckTime : ℝ) : ℝ :=
  (P.dimensionlessTime : ℝ) * planckTime

/-- Every finite non-empty Sigma patch has at least one Planck-clock tick. -/
lemma one_le_dimensionlessTime :
    1 ≤ P.dimensionlessTime := by
  classical
  rcases P.nonempty_edges with ⟨e₀⟩
  have hsingle :
      P.clockCount e₀ ≤ Finset.univ.sum P.clockCount :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ e₀)
  exact le_trans (P.clockCount_pos e₀) hsingle

/--
The physical patch time is bounded below by the Planck time whenever the Planck
time parameter is non-negative.
-/
lemma planckTime_le_patchTime {planckTime : ℝ} (hPlanck : 0 ≤ planckTime) :
    planckTime ≤ P.patchTime planckTime := by
  have hdim : (1 : ℝ) ≤ (P.dimensionlessTime : ℝ) := by
    exact_mod_cast P.one_le_dimensionlessTime
  calc
    planckTime = (1 : ℝ) * planckTime := by ring
    _ ≤ (P.dimensionlessTime : ℝ) * planckTime :=
      mul_le_mul_of_nonneg_right hdim hPlanck
    _ = P.patchTime planckTime := rfl

/-- Positive Planck time gives positive patch time. -/
lemma patchTime_pos {planckTime : ℝ} (hPlanck : 0 < planckTime) :
    0 < P.patchTime planckTime := by
  have hdim : (0 : ℝ) < (P.dimensionlessTime : ℝ) := by
    exact_mod_cast lt_of_lt_of_le Nat.zero_lt_one P.one_le_dimensionlessTime
  exact mul_pos hdim hPlanck

end FiniteSigmaPatch

/--
Representative/readout stability datum.  No linearity is required for the
finite threshold statement: the only needed hypothesis is a uniform lower norm
bound on the selected representative domain.
-/
structure RepresentativeStabilityDatum (Domain Target : Type*)
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target] where
  readout : Domain → Target
  stabilityConstant : ℝ
  stabilityConstant_pos : 0 < stabilityConstant
  stable : ∀ x : Domain, stabilityConstant * ‖x‖ ≤ ‖readout x‖

namespace RepresentativeStabilityDatum

variable {Domain Target : Type*}
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (R : RepresentativeStabilityDatum Domain Target)

/-- A stable representative readout has no non-zero vector in its kernel. -/
lemma eq_zero_of_readout_eq_zero {x : Domain} (hx : R.readout x = 0) :
    x = 0 := by
  have hle : R.stabilityConstant * ‖x‖ ≤ 0 := by
    simpa [hx] using R.stable x
  have hnonneg : 0 ≤ R.stabilityConstant * ‖x‖ :=
    mul_nonneg (le_of_lt R.stabilityConstant_pos) (norm_nonneg x)
  have hmul : R.stabilityConstant * ‖x‖ = 0 :=
    le_antisymm hle hnonneg
  have hnorm : ‖x‖ = 0 := by
    rcases mul_eq_zero.mp hmul with hconst | hnorm
    · exact False.elim ((ne_of_gt R.stabilityConstant_pos) hconst)
    · exact hnorm
  exact norm_eq_zero.mp hnorm

/-- A stable representative readout is injective on equal readout fibers over zero. -/
lemma readout_zero_iff {x : Domain} :
    R.readout x = 0 → x = 0 :=
  R.eq_zero_of_readout_eq_zero

/-- Stability gives the standard inverse-norm bound on the readout image. -/
lemma norm_le_inv_mul_norm_readout (x : Domain) :
    ‖x‖ ≤ R.stabilityConstant⁻¹ * ‖R.readout x‖ := by
  have hdiv : ‖x‖ ≤ ‖R.readout x‖ / R.stabilityConstant := by
    rw [le_div_iff₀ R.stabilityConstant_pos]
    simpa [mul_comm] using R.stable x
  simpa [div_eq_inv_mul, mul_comm] using hdiv

end RepresentativeStabilityDatum

/-- Finite real collapse-kernel parameters. -/
structure CollapseKernelParameters where
  threshold : ℝ
  threshold_pos : 0 < threshold
  exponent : ℕ
  exponent_pos : 0 < exponent

namespace CollapseKernelParameters

/--
Finite real collapse contribution of one patch edge.  The Heaviside convention
is encoded by the `if threshold <= |deltaSigma|` branch.
-/
def realContribution (K : CollapseKernelParameters) (weight deltaSigma : ℝ) :
    ℝ :=
  if K.threshold ≤ |deltaSigma| then
    weight * (|deltaSigma| / K.threshold) ^ K.exponent
  else
    0

lemma realContribution_eq_zero_of_inactive
    (K : CollapseKernelParameters) {weight deltaSigma : ℝ}
    (hinactive : |deltaSigma| < K.threshold) :
    K.realContribution weight deltaSigma = 0 := by
  simp [realContribution, not_le.mpr hinactive]

lemma realContribution_pos_of_active
    (K : CollapseKernelParameters) {weight deltaSigma : ℝ}
    (hweight : 0 < weight) (hactive : K.threshold ≤ |deltaSigma|) :
    0 < K.realContribution weight deltaSigma := by
  have hAbs : 0 < |deltaSigma| :=
    lt_of_lt_of_le K.threshold_pos hactive
  have hratio : 0 < |deltaSigma| / K.threshold :=
    div_pos hAbs K.threshold_pos
  rw [realContribution, if_pos hactive]
  exact mul_pos hweight (pow_pos hratio K.exponent)

lemma realContribution_nonneg
    (K : CollapseKernelParameters) {weight deltaSigma : ℝ}
    (hweight : 0 < weight) :
    0 ≤ K.realContribution weight deltaSigma := by
  by_cases hactive : K.threshold ≤ |deltaSigma|
  · exact le_of_lt (K.realContribution_pos_of_active hweight hactive)
  · simp [realContribution, hactive]

end CollapseKernelParameters

namespace FiniteSigmaPatch

variable {Edge : Type*} [Fintype Edge] (P : FiniteSigmaPatch Edge)

/-- Finite patch collapse action. -/
def collapseAction (K : CollapseKernelParameters) : ℝ :=
  Finset.univ.sum fun e =>
    K.realContribution (P.weight e) (P.deltaSigma e)

/-- Finite collapse actions are non-negative. -/
lemma collapseAction_nonneg (K : CollapseKernelParameters) :
    0 ≤ P.collapseAction K := by
  classical
  exact Finset.sum_nonneg fun e _ =>
    K.realContribution_nonneg (P.weight_pos e)

/-- If every edge is below threshold, the finite collapse action vanishes. -/
lemma collapseAction_eq_zero_of_all_inactive
    (K : CollapseKernelParameters)
    (hinactive : ∀ e, |P.deltaSigma e| < K.threshold) :
    P.collapseAction K = 0 := by
  classical
  simp [collapseAction, K.realContribution_eq_zero_of_inactive, hinactive]

/-- If one edge is at or above threshold, the finite collapse action is positive. -/
lemma collapseAction_pos_of_exists_active
    (K : CollapseKernelParameters)
    (hactive : ∃ e, K.threshold ≤ |P.deltaSigma e|) :
    0 < P.collapseAction K := by
  classical
  rcases hactive with ⟨e₀, h₀⟩
  have hpos :
      0 < K.realContribution (P.weight e₀) (P.deltaSigma e₀) :=
    K.realContribution_pos_of_active (P.weight_pos e₀) h₀
  have hsingle :
      K.realContribution (P.weight e₀) (P.deltaSigma e₀) ≤
        Finset.univ.sum fun e =>
          K.realContribution (P.weight e) (P.deltaSigma e) :=
    Finset.single_le_sum
      (fun e _ => K.realContribution_nonneg (P.weight_pos e))
      (Finset.mem_univ e₀)
  exact lt_of_lt_of_le hpos hsingle

end FiniteSigmaPatch

/-- External scalar visibility envelope for finite collapse action `A`. -/
def externalVisibility (A : ℝ) : ℝ :=
  Real.exp (-A)

lemma externalVisibility_pos (A : ℝ) :
    0 < externalVisibility A :=
  Real.exp_pos (-A)

lemma externalVisibility_ne_zero (A : ℝ) :
    externalVisibility A ≠ 0 :=
  ne_of_gt (externalVisibility_pos A)

/--
The finite visibility threshold: visibility is below resolution `epsilon` iff
the collapse action crosses the logarithmic threshold.
-/
theorem externalVisibility_le_iff_log_inv_le
    {A epsilon : ℝ} (hepsilon : 0 < epsilon) :
    externalVisibility A ≤ epsilon ↔ Real.log epsilon⁻¹ ≤ A := by
  have hmain :
      externalVisibility A ≤ epsilon ↔ -A ≤ Real.log epsilon := by
    simpa [externalVisibility] using
      (Real.le_log_iff_exp_le (x := -A) hepsilon).symm
  rw [hmain, Real.log_inv]
  constructor <;> intro h <;> linarith

theorem externalVisibility_le_of_log_inv_le
    {A epsilon : ℝ} (hepsilon : 0 < epsilon)
    (hthreshold : Real.log epsilon⁻¹ ≤ A) :
    externalVisibility A ≤ epsilon :=
  (externalVisibility_le_iff_log_inv_le hepsilon).mpr hthreshold

/--
Finite damping alone never gives exact zero external visibility.  Exact loss at
finite damping must come from a non-injective readout/projection rather than
from the scalar exponential envelope.
-/
theorem finite_damping_not_exact_zero (A : ℝ) :
    externalVisibility A ≠ 0 :=
  externalVisibility_ne_zero A

/-- Predicate: a patch is temporally carried at the supplied Planck time. -/
def TemporallyCarried {Edge : Type*} [Fintype Edge]
    (P : FiniteSigmaPatch Edge) (planckTime : ℝ) : Prop :=
  planckTime ≤ P.patchTime planckTime

/-- Predicate: the supplied readout has no non-zero representative kernel. -/
def RepresentativeStable {Domain Target : Type*}
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (R : RepresentativeStabilityDatum Domain Target) : Prop :=
  ∀ x : Domain, R.readout x = 0 → x = 0

/--
Predicate: scalar collapse damping makes the patch externally invisible at the
given resolution.
-/
def CollapseReadoutInvisibleAt (A epsilon : ℝ) : Prop :=
  externalVisibility A ≤ epsilon

/--
Predicate: scalar collapse damping keeps the patch externally visible at the
given resolution.
-/
def CollapseReadoutVisibleAt (A epsilon : ℝ) : Prop :=
  epsilon < externalVisibility A

/-- Predicate: finite scalar damping has not produced exact zero visibility. -/
def FiniteDampingNonzero (A : ℝ) : Prop :=
  externalVisibility A ≠ 0

/--
Predicate: an external readout is incomplete while the completed finite residual
evolution remains information-preserving.
-/
def ProjectionIncompleteWithoutInternalLoss
    {Ext Comp Therm : Type*} [Fintype Ext] [Fintype Comp]
    (D : SigmaProofs.HorizonReadout.FiniteResidualCompletion Ext Comp)
    (readout : Ext → Therm) : Prop :=
  D.ExternalReadoutIncomplete readout ∧ ¬ D.InternalInformationLoss

lemma temporallyCarried_of_sigmaP
    {Edge : Type*} [Fintype Edge]
    (P : FiniteSigmaPatch Edge) {planckTime : ℝ}
    (hPlanck : 0 ≤ planckTime) :
    TemporallyCarried P planckTime :=
  P.planckTime_le_patchTime hPlanck

lemma representativeStable_of_stabilityDatum
    {Domain Target : Type*}
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (R : RepresentativeStabilityDatum Domain Target) :
    RepresentativeStable R :=
  fun _ hx => R.eq_zero_of_readout_eq_zero hx

lemma collapseReadoutInvisibleAt_iff_log_threshold
    {A epsilon : ℝ} (hepsilon : 0 < epsilon) :
    CollapseReadoutInvisibleAt A epsilon ↔ Real.log epsilon⁻¹ ≤ A :=
  externalVisibility_le_iff_log_inv_le hepsilon

lemma collapseReadoutVisibleAt_iff_not_log_threshold
    {A epsilon : ℝ} (hepsilon : 0 < epsilon) :
    CollapseReadoutVisibleAt A epsilon ↔ ¬ Real.log epsilon⁻¹ ≤ A := by
  rw [CollapseReadoutVisibleAt, ← not_le, externalVisibility_le_iff_log_inv_le hepsilon]

lemma finiteDampingNonzero (A : ℝ) :
    FiniteDampingNonzero A :=
  finite_damping_not_exact_zero A

lemma projectionIncompleteWithoutInternalLoss_of_readoutIncomplete
    {Ext Comp Therm : Type*} [Fintype Ext] [Fintype Comp]
    (D : SigmaProofs.HorizonReadout.FiniteResidualCompletion Ext Comp)
    (readout : Ext → Therm)
    (hincomplete : D.ExternalReadoutIncomplete readout) :
    ProjectionIncompleteWithoutInternalLoss D readout :=
  ⟨hincomplete, D.no_internal_information_loss⟩

/--
A raw readout datum has no built-in stability assumption.  It is used to state
the Sigma admissibility bridge without making representative stability
definitionally automatic.
-/
structure ReadoutDatum (Domain Target : Type*)
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target] where
  readout : Domain → Target

namespace ReadoutDatum

variable {Domain Target : Type*}
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]

/-- Faithfulness of a raw readout on its representative domain. -/
def Faithful (Q : ReadoutDatum Domain Target) : Prop :=
  ∀ x : Domain, Q.readout x = 0 → x = 0

/-- The zero readout datum, used to state that admissibility excludes it when visible. -/
def zero (Domain Target : Type*)
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target] :
    ReadoutDatum Domain Target where
  readout := fun _ => 0

end ReadoutDatum

/--
Visibility-faithful readout bridge.  It expresses the Sigma admissibility rule:
a readout compatible with the collapse visibility kernel cannot erase a
temporally carried patch while that patch remains externally visible.
-/
structure VisibilityFaithfulReadout
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (Q : ReadoutDatum Domain Target)
    (K : CollapseKernelParameters)
    (planckTime epsilon : ℝ) : Prop where
  faithful_of_visible :
    TemporallyCarried P planckTime →
      CollapseReadoutVisibleAt (P.collapseAction K) epsilon →
        Q.Faithful

/--
A Sigma-admissible readout is a visibility-faithful readout.  This is a
definition of admissibility, not an identification of temporal support,
collapse visibility, and representative faithfulness.
-/
abbrev SigmaAdmissibleReadout
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (Q : ReadoutDatum Domain Target)
    (K : CollapseKernelParameters)
    (planckTime epsilon : ℝ) : Prop :=
  VisibilityFaithfulReadout P Q K planckTime epsilon

/-- A visibility-faithful readout is faithful on visible temporally carried patches. -/
theorem visibilityFaithfulReadout_yields_faithful_of_visible
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    {P : FiniteSigmaPatch Edge}
    {Q : ReadoutDatum Domain Target}
    {K : CollapseKernelParameters}
    {planckTime epsilon : ℝ}
    (H : VisibilityFaithfulReadout P Q K planckTime epsilon)
    (htemporal : TemporallyCarried P planckTime)
    (hvisible : CollapseReadoutVisibleAt (P.collapseAction K) epsilon) :
    Q.Faithful :=
  H.faithful_of_visible htemporal hvisible

/--
Under `sigma.P` temporal support, a Sigma-admissible readout is faithful whenever
the collapse kernel classifies the patch as externally visible.
-/
theorem sigmaAdmissibleReadout_faithful_of_sigmaP_and_visible
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    {Q : ReadoutDatum Domain Target}
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (H : SigmaAdmissibleReadout P Q K planckTime epsilon)
    (hPlanck : 0 ≤ planckTime)
    (hvisible : CollapseReadoutVisibleAt (P.collapseAction K) epsilon) :
    Q.Faithful :=
  H.faithful_of_visible (temporallyCarried_of_sigmaP P hPlanck) hvisible

/--
A completely zero readout cannot be Sigma-admissible on a visible temporally
carried patch if the representative domain contains a non-zero element.
-/
theorem not_sigmaAdmissible_zeroReadout_of_visible_nonzero
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime)
    (hvisible : CollapseReadoutVisibleAt (P.collapseAction K) epsilon)
    {x : Domain} (hx : x ≠ 0) :
    ¬ SigmaAdmissibleReadout P (ReadoutDatum.zero Domain Target) K planckTime epsilon := by
  intro H
  have hfaith :
      (ReadoutDatum.zero Domain Target).Faithful :=
    sigmaAdmissibleReadout_faithful_of_sigmaP_and_visible
      P K H hPlanck hvisible
  exact hx (hfaith x rfl)

/--
Finite access classes for a patch/readout pair at a chosen external resolution.
The classes are predicates rather than exclusive constructors: a physical
configuration can be temporally carried, representative-stable, and externally
invisible at the same time.
-/
structure PatchAccessClassification
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    (planckTime epsilon : ℝ) : Prop where
  temporally_carried : TemporallyCarried P planckTime
  representative_stable : RepresentativeStable R
  visibility_threshold :
    CollapseReadoutInvisibleAt (P.collapseAction K) epsilon ↔
      Real.log epsilon⁻¹ ≤ P.collapseAction K
  finite_damping_nonzero : FiniteDampingNonzero (P.collapseAction K)

/-- The three threshold assumptions produce the explicit access classification. -/
theorem patchAccessClassification
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime) (hepsilon : 0 < epsilon) :
    PatchAccessClassification P R K planckTime epsilon where
  temporally_carried := temporallyCarried_of_sigmaP P hPlanck
  representative_stable := representativeStable_of_stabilityDatum R
  visibility_threshold := collapseReadoutInvisibleAt_iff_log_threshold hepsilon
  finite_damping_nonzero := finiteDampingNonzero (P.collapseAction K)

/--
Bundled class: a patch is admissible and externally visible at the chosen
resolution.  This packages the three predicates without identifying them.
-/
structure AdmissibleVisiblePatch
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    (planckTime epsilon : ℝ) : Prop where
  temporal : TemporallyCarried P planckTime
  representative : RepresentativeStable R
  visible : CollapseReadoutVisibleAt (P.collapseAction K) epsilon

/--
Bundled class: a patch is admissible but externally invisible at the chosen
resolution.  Finite damping remains non-zero, so this is not exact scalar
annihilation.
-/
structure AdmissibleExternallyInvisiblePatch
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    (planckTime epsilon : ℝ) : Prop where
  temporal : TemporallyCarried P planckTime
  representative : RepresentativeStable R
  invisible : CollapseReadoutInvisibleAt (P.collapseAction K) epsilon
  finite_damping_nonzero : FiniteDampingNonzero (P.collapseAction K)

/-- Constructor for the bundled admissible-visible patch class. -/
theorem admissibleVisiblePatch_of_visible
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime)
    (hvisible : CollapseReadoutVisibleAt (P.collapseAction K) epsilon) :
    AdmissibleVisiblePatch P R K planckTime epsilon where
  temporal := temporallyCarried_of_sigmaP P hPlanck
  representative := representativeStable_of_stabilityDatum R
  visible := hvisible

/-- Constructor for the bundled admissible-but-externally-invisible patch class. -/
theorem admissibleExternallyInvisiblePatch_of_invisible
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime)
    (hinvisible : CollapseReadoutInvisibleAt (P.collapseAction K) epsilon) :
    AdmissibleExternallyInvisiblePatch P R K planckTime epsilon where
  temporal := temporallyCarried_of_sigmaP P hPlanck
  representative := representativeStable_of_stabilityDatum R
  invisible := hinvisible
  finite_damping_nonzero := finiteDampingNonzero (P.collapseAction K)

/--
Visible and externally invisible bundled classes share the same temporal and
representative admissibility predicates; they differ only in the external
visibility predicate.
-/
theorem visible_invisible_classes_share_admissibility
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    {P : FiniteSigmaPatch Edge}
    {R : RepresentativeStabilityDatum Domain Target}
    {K : CollapseKernelParameters}
    {planckTime epsilon₁ epsilon₂ : ℝ}
    (V : AdmissibleVisiblePatch P R K planckTime epsilon₁)
    (I : AdmissibleExternallyInvisiblePatch P R K planckTime epsilon₂) :
    TemporallyCarried P planckTime ∧ RepresentativeStable R ∧
      CollapseReadoutVisibleAt (P.collapseAction K) epsilon₁ ∧
      CollapseReadoutInvisibleAt (P.collapseAction K) epsilon₂ := by
  exact ⟨V.temporal, V.representative, V.visible, I.invisible⟩

/--
The explicit class-level separation: external collapse invisibility at a finite
resolution coexists with positive temporal support, representative stability,
and non-zero finite scalar visibility.
-/
theorem collapseInvisible_class_separates_from_temporal_and_exact_zero
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime)
    (hinvisible : CollapseReadoutInvisibleAt (P.collapseAction K) epsilon) :
    TemporallyCarried P planckTime ∧
      RepresentativeStable R ∧
      CollapseReadoutInvisibleAt (P.collapseAction K) epsilon ∧
      FiniteDampingNonzero (P.collapseAction K) := by
  exact ⟨temporallyCarried_of_sigmaP P hPlanck,
    representativeStable_of_stabilityDatum R,
    hinvisible,
    finiteDampingNonzero (P.collapseAction K)⟩

/--
Combined finite patch criterion: positive Planck-clock support, representative
stability, and the logarithmic collapse-readout visibility threshold.
-/
theorem threeThresholdSeparation
    {Edge Domain Target : Type*} [Fintype Edge]
    [NormedAddCommGroup Domain] [SeminormedAddCommGroup Target]
    (P : FiniteSigmaPatch Edge)
    (R : RepresentativeStabilityDatum Domain Target)
    (K : CollapseKernelParameters)
    {planckTime epsilon : ℝ}
    (hPlanck : 0 ≤ planckTime) (hepsilon : 0 < epsilon) :
    planckTime ≤ P.patchTime planckTime ∧
      (∀ x : Domain, R.readout x = 0 → x = 0) ∧
      (externalVisibility (P.collapseAction K) ≤ epsilon ↔
        Real.log epsilon⁻¹ ≤ P.collapseAction K) := by
  exact ⟨P.planckTime_le_patchTime hPlanck,
    (fun x hx => R.readout_zero_iff hx),
    externalVisibility_le_iff_log_inv_le hepsilon⟩

/--
Patch visibility is compatible with the existing finite horizon-readout
separation theorem: the scalar visibility threshold is an external readout
statement, while the completed residual finite equivalence is injective.
-/
theorem patchVisibility_with_finiteReadoutSeparation
    {Ext Comp Therm : Type*} [Fintype Ext] [Fintype Comp]
    (D : SigmaProofs.HorizonReadout.FiniteResidualCompletion Ext Comp)
    (readout : Ext → Therm)
    (hincomplete : D.ExternalReadoutIncomplete readout)
    {A epsilon : ℝ} (hepsilon : 0 < epsilon) :
    (externalVisibility A ≤ epsilon ↔ Real.log epsilon⁻¹ ≤ A) ∧
      ¬ D.InternalInformationLoss ∧ D.ExternalReadoutIncomplete readout := by
  exact ⟨externalVisibility_le_iff_log_inv_le hepsilon,
    D.no_internal_information_loss,
    hincomplete⟩

end

end SigmaProofs.PatchVisibility
