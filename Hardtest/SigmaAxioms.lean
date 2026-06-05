/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.BlockLaplacian

/-!
# Finite Sigma axiom model

This file contains the finite transition-level model for the Appendix VI Sigma
postulate package.  It depends on the concrete four-dimensional fine-edge and
block-star data from `Hardtest.BlockLaplacian`, but keeps the joint axiom model
separate from the block-Laplacian and spectral arguments.
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

def concreteSigmaAxiomSystem4 (L : ℕ) (hL : 4 ≤ L) :
    SigmaAxiomSystem4 L hL where
  sigmaP_clock := sigma4PlanckNoZeroClock L
  sigma1_to_sigma4 := concreteSigmaPhysicalAxioms4 L hL
  sigmaP_clock_matches_time := by
    intro e
    rfl
  sigma5_causality_preservation := by
    intro e f hcomp hepos hfpos
    have hsum := sigmaComposableTimeSub_eq_tension_add hcomp
    change 0 ≤ sigmaCoord4Time (sigmaFineEdgeTarget f) -
      sigmaCoord4Time (sigmaFineEdgeSource e)
    rw [hsum]
    change 0 < sigmaOrientationTension e at hepos
    change 0 < sigmaOrientationTension f at hfpos
    nlinarith
  sigma6_bounded_tension := by
    refine ⟨1, 1, by norm_num, by norm_num, ?_⟩
    intro e
    change 1 ≤ |sigmaOrientationTension e| ∧ |sigmaOrientationTension e| ≤ 1
    rw [sigmaOrientationTension_abs_eq_one e]
    exact ⟨le_rfl, le_rfl⟩
  sigma7_triangle_bound := by
    refine ⟨1, by norm_num, ?_⟩
    intro e f hcomp
    have hsum := sigmaComposableTimeSub_eq_tension_add hcomp
    simpa [concreteSigmaPhysicalAxioms4] using by
      rw [hsum]
      norm_num

theorem sigmaAxiomSystem4_nonempty (L : ℕ) (hL : 4 ≤ L) :
    Nonempty (SigmaAxiomSystem4 L hL) :=
  ⟨concreteSigmaAxiomSystem4 L hL⟩

end Hardtest
