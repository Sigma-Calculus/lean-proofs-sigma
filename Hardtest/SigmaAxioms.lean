/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.BlockLaplacian

/-!
# Finite Sigma dynamics and axiom model

This file contains the finite transition-level framework for the Appendix VI
Sigma postulate package.  It defines an admissible finite Sigma dynamics class,
proves that every such dynamics induces the joint `sigma.P` and
`sigma.1`--`sigma.7` axiom model, and provides the concrete four-dimensional
block-star instance.  It depends on the fine-edge and block-star data from
`Hardtest.BlockLaplacian`, but keeps the dynamics and axiom layer separate from
the block-Laplacian and spectral arguments.
-/

namespace Hardtest

lemma sigmaOrientationTension_abs_eq_one {L : ℕ}
    (e : SigmaFineEdge4 L) :
    |sigmaOrientationTension e| = 1 := by
  cases hf : sigmaFineEdgeForward e <;>
    norm_num [sigmaOrientationTension, hf]

lemma sigmaComposableTimeSub_eq_tension_add {L : ℕ}
    {e f : SigmaFineEdge4 L}
    (hcomp : sigmaFineEdgeTarget e = sigmaFineEdgeSource f) :
    sigmaCoord4Time (sigmaFineEdgeTarget f) -
        sigmaCoord4Time (sigmaFineEdgeSource e) =
      sigmaOrientationTension e + sigmaOrientationTension f := by
  have he := sigmaCoord4Time_target_sub_source e
  have hf := sigmaCoord4Time_target_sub_source f
  rw [← he, ← hf, ← hcomp]
  ring

/--
Joint finite Sigma axiom model for Appendix VI.  The quantified domain is the
admissible elementary fine-edge transitions and their composable pairs, not all
unrelated event pairs.
-/
structure SigmaAxiomSystem4 (L : ℕ) (hL : 4 ≤ L) where
  sigmaP_clock : SigmaPlanckNoZeroClock (SigmaFineEdge4 L)
  sigma1_to_sigma4 : SigmaPhysicalAxioms4 L hL
  sigmaP_clock_matches_time :
    ∀ e,
      sigmaP_clock.primitiveTime e =
        |sigma1_to_sigma4.eventTime (sigmaFineEdgeTarget e) -
          sigma1_to_sigma4.eventTime (sigmaFineEdgeSource e)|
  sigma5_causality_preservation :
    ∀ {e f : SigmaFineEdge4 L},
      sigmaFineEdgeTarget e = sigmaFineEdgeSource f →
        0 < sigma1_to_sigma4.tension e →
          0 < sigma1_to_sigma4.tension f →
            0 ≤ sigma1_to_sigma4.eventTime (sigmaFineEdgeTarget f) -
              sigma1_to_sigma4.eventTime (sigmaFineEdgeSource e)
  sigma6_bounded_tension :
    ∃ sigmaMin sigmaMax : ℝ,
      0 < sigmaMin ∧ sigmaMin ≤ sigmaMax ∧
        ∀ e : SigmaFineEdge4 L,
          sigmaMin ≤ |sigma1_to_sigma4.tension e| ∧
            |sigma1_to_sigma4.tension e| ≤ sigmaMax
  sigma7_triangle_bound :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {e f : SigmaFineEdge4 L},
        sigmaFineEdgeTarget e = sigmaFineEdgeSource f →
          |(sigma1_to_sigma4.eventTime (sigmaFineEdgeTarget f) -
              sigma1_to_sigma4.eventTime (sigmaFineEdgeSource e)) -
                (sigma1_to_sigma4.tension e + sigma1_to_sigma4.tension f)| ≤
            delta

/--
Admissible finite Sigma dynamics for the Appendix VI transition layer.  This is
not a smooth or variational time evolution; it is the finite transition class
from which the displayed Sigma postulates are read off.
-/
structure SigmaAdmissibleDynamics4 (L : ℕ) (hL : 4 ≤ L) where
  clock : SigmaPlanckNoZeroClock (SigmaFineEdge4 L)
  eventTime : SigmaCoord4 L → ℝ
  localScale : SigmaFineEdge4 L → ℝ
  tension : SigmaFineEdge4 L → ℝ
  edgeReverse : SigmaFineEdge4 L → SigmaFineEdge4 L
  reverse_source :
    ∀ e, sigmaFineEdgeSource (edgeReverse e) = sigmaFineEdgeTarget e
  reverse_target :
    ∀ e, sigmaFineEdgeTarget (edgeReverse e) = sigmaFineEdgeSource e
  reverse_scale :
    ∀ e, localScale (edgeReverse e) = localScale e
  localScale_pos :
    ∀ e, 0 < localScale e
  tension_eq_time_div_scale :
    ∀ e,
      tension e =
        (eventTime (sigmaFineEdgeTarget e) -
            eventTime (sigmaFineEdgeSource e)) / localScale e
  clock_matches_time :
    ∀ e,
      clock.primitiveTime e =
        |eventTime (sigmaFineEdgeTarget e) -
          eventTime (sigmaFineEdgeSource e)|
  tension_lipschitz :
    ∃ C : ℝ, 0 < C ∧
      ∀ e f : SigmaFineEdge4 L,
        |tension e - tension f| ≤ C * sigmaFineEdgeTensionDistance e f
  positive_chain_time_nonneg :
    ∀ {e f : SigmaFineEdge4 L},
      sigmaFineEdgeTarget e = sigmaFineEdgeSource f →
        0 < tension e →
          0 < tension f →
            0 ≤ eventTime (sigmaFineEdgeTarget f) -
              eventTime (sigmaFineEdgeSource e)
  tension_bounds :
    ∃ sigmaMin sigmaMax : ℝ,
      0 < sigmaMin ∧ sigmaMin ≤ sigmaMax ∧
        ∀ e : SigmaFineEdge4 L,
          sigmaMin ≤ |tension e| ∧ |tension e| ≤ sigmaMax
  additive_defect_bound :
    ∃ delta : ℝ, 0 < delta ∧
      ∀ {e f : SigmaFineEdge4 L},
        sigmaFineEdgeTarget e = sigmaFineEdgeSource f →
          |(eventTime (sigmaFineEdgeTarget f) -
              eventTime (sigmaFineEdgeSource e)) -
                (tension e + tension f)| ≤ delta

namespace SigmaAdmissibleDynamics4

variable {L : ℕ} {hL : 4 ≤ L} (D : SigmaAdmissibleDynamics4 L hL)

lemma primitive_abs_time_pos (e : SigmaFineEdge4 L) :
    0 < |D.eventTime (sigmaFineEdgeTarget e) -
      D.eventTime (sigmaFineEdgeSource e)| := by
  rw [← D.clock_matches_time e]
  exact SigmaPlanckNoZeroClock.primitiveTime_pos D.clock e

lemma time_sub_ne_zero (e : SigmaFineEdge4 L) :
    D.eventTime (sigmaFineEdgeTarget e) -
      D.eventTime (sigmaFineEdgeSource e) ≠ 0 := by
  exact abs_pos.mp (D.primitive_abs_time_pos e)

lemma tension_ne_zero (e : SigmaFineEdge4 L) :
    D.tension e ≠ 0 := by
  rw [D.tension_eq_time_div_scale e]
  exact div_ne_zero (D.time_sub_ne_zero e) (ne_of_gt (D.localScale_pos e))

lemma reverse_tension (e : SigmaFineEdge4 L) :
    D.tension (D.edgeReverse e) = -D.tension e := by
  rw [D.tension_eq_time_div_scale (D.edgeReverse e),
    D.tension_eq_time_div_scale e, D.reverse_source e, D.reverse_target e,
    D.reverse_scale e]
  ring

def toSigmaPhysicalAxioms4 : SigmaPhysicalAxioms4 L hL where
  eventTime := D.eventTime
  localScale := D.localScale
  tension := D.tension
  edgeReverse := D.edgeReverse
  reverse_source := D.reverse_source
  reverse_target := D.reverse_target
  sigma1_scale_pos := D.localScale_pos
  sigma1_tension_eq_time_div_scale := D.tension_eq_time_div_scale
  sigma2_tension_nonzero := D.tension_ne_zero
  sigma3_reverse_tension := D.reverse_tension
  sigma4_lipschitz := D.tension_lipschitz

def toSigmaAxiomSystem4 : SigmaAxiomSystem4 L hL where
  sigmaP_clock := D.clock
  sigma1_to_sigma4 := D.toSigmaPhysicalAxioms4
  sigmaP_clock_matches_time := D.clock_matches_time
  sigma5_causality_preservation := D.positive_chain_time_nonneg
  sigma6_bounded_tension := D.tension_bounds
  sigma7_triangle_bound := D.additive_defect_bound

end SigmaAdmissibleDynamics4

def concreteSigmaAdmissibleDynamics4 (L : ℕ) (hL : 4 ≤ L) :
    SigmaAdmissibleDynamics4 L hL where
  clock := sigma4PlanckNoZeroClock L
  eventTime := sigmaCoord4Time
  localScale := fun _ => 1
  tension := sigmaOrientationTension
  edgeReverse := sigmaFineEdgeReverse
  reverse_source := sigmaFineEdgeReverse_source
  reverse_target := sigmaFineEdgeReverse_target
  reverse_scale := by
    intro e
    rfl
  localScale_pos := by
    intro e
    norm_num
  tension_eq_time_div_scale := by
    intro e
    rw [sigmaCoord4Time_target_sub_source]
    norm_num
  clock_matches_time := by
    intro e
    rfl
  tension_lipschitz := sigmaOrientationTension_lipschitz
  positive_chain_time_nonneg := by
    intro e f hcomp hepos hfpos
    have hsum := sigmaComposableTimeSub_eq_tension_add hcomp
    change 0 ≤ sigmaCoord4Time (sigmaFineEdgeTarget f) -
      sigmaCoord4Time (sigmaFineEdgeSource e)
    rw [hsum]
    change 0 < sigmaOrientationTension e at hepos
    change 0 < sigmaOrientationTension f at hfpos
    nlinarith
  tension_bounds := by
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro e
    rw [sigmaOrientationTension_abs_eq_one e]
    exact ⟨le_rfl, le_rfl⟩
  additive_defect_bound := by
    refine ⟨1, by norm_num, ?_⟩
    intro e f hcomp
    have hsum := sigmaComposableTimeSub_eq_tension_add hcomp
    rw [hsum]
    norm_num

theorem sigmaAdmissibleDynamics4_nonempty (L : ℕ) (hL : 4 ≤ L) :
    Nonempty (SigmaAdmissibleDynamics4 L hL) :=
  ⟨concreteSigmaAdmissibleDynamics4 L hL⟩

theorem sigmaAdmissibleDynamics4_implies_axiomSystem4
    {L : ℕ} {hL : 4 ≤ L} (D : SigmaAdmissibleDynamics4 L hL) :
    Nonempty (SigmaAxiomSystem4 L hL) :=
  ⟨D.toSigmaAxiomSystem4⟩

def concreteSigmaAxiomSystem4 (L : ℕ) (hL : 4 ≤ L) :
    SigmaAxiomSystem4 L hL :=
  (concreteSigmaAdmissibleDynamics4 L hL).toSigmaAxiomSystem4

theorem sigmaAxiomSystem4_nonempty (L : ℕ) (hL : 4 ≤ L) :
    Nonempty (SigmaAxiomSystem4 L hL) :=
  ⟨concreteSigmaAxiomSystem4 L hL⟩

end Hardtest
