/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.DiscreteNoether
import Hardtest.SourceConfluence

/-!
# Source-generated discrete Noether realization

This module connects the concrete source-confluence construction in
`Hardtest/SourceConfluence.lean` with the finite reduced Noether layer in
`Hardtest/DiscreteNoether.lean`.

## TeX correspondence

The paper-facing source is `discrete_noether_sigma_v3.tex`, in particular the
results titled "The parallel-channel harmonic sector is the augmentation-zero
module", "The canonical parallel-channel cycles supply the period frame", and
"Canonical non-scalar response action on the parallel-channel complex".

The construction below acts on the four-source Euclidean augmentation kernel.
It proves that the concrete cyclic source transition induces an orthogonal
order-four action, packages that action as cyclic reduced Noether data, and
exhibits vectors on which the resulting charge is not a scalar multiple of the
norm squared.  This is the rank-three source-generated model.  It does not
identify an independently prescribed physical transition network with the
canonical parallel-channel response complex.
-/

namespace Hardtest
namespace SourceNoether

noncomputable section

open scoped BigOperators
open GaugeTransport
open GaugeTransport.FiniteTransportComplex
open SourceConfluence
open SourceConfluence.ConcreteFourCoordinateModel

/-- Euclidean coefficient space of the four registered source atoms. -/
abbrev FourSourceSpace := EuclideanSpace ℝ (Fin 4)

/-- The source augmentation functional is the sum of the four coefficients. -/
noncomputable def fourSourceAugmentation : FourSourceSpace →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' r x := by simp [Finset.mul_sum]

/-- Rank-three augmentation-null source carrier. -/
abbrev FourSourceAugmentationSpace :=
  LinearMap.ker fourSourceAugmentation

/-- The concrete four-cycle acts isometrically on all source coefficients. -/
noncomputable def fourSourceCycle :
    FourSourceSpace ≃ₗᵢ[ℝ] FourSourceSpace :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ axisCycle

@[simp]
theorem fourSourceCycle_apply
    (x : FourSourceSpace) (j : Fin 4) :
    fourSourceCycle x j = x (axisCycle.symm j) :=
  rfl

/-- Cyclic source relabeling preserves the augmentation functional. -/
theorem fourSourceAugmentation_cycle
    (x : FourSourceSpace) :
    fourSourceAugmentation (fourSourceCycle x) =
      fourSourceAugmentation x := by
  change (∑ j, x (axisCycle.symm j)) = ∑ j, x j
  exact axisCycle.symm.sum_comp x

/-- The inverse cyclic source relabeling also preserves augmentation. -/
theorem fourSourceAugmentation_cycle_symm
    (x : FourSourceSpace) :
    fourSourceAugmentation (fourSourceCycle.symm x) =
      fourSourceAugmentation x := by
  change (∑ j, x (axisCycle j)) = ∑ j, x j
  exact axisCycle.symm.symm.sum_comp x

/-- Restriction of the concrete source cycle to the rank-three
augmentation-null carrier. -/
noncomputable def fourSourceAugmentationCycle :
    FourSourceAugmentationSpace ≃ₗᵢ[ℝ] FourSourceAugmentationSpace where
  toLinearEquiv :=
    { toFun := fun x =>
        ⟨fourSourceCycle x.1, by
          change fourSourceAugmentation (fourSourceCycle x.1) = 0
          rw [fourSourceAugmentation_cycle]
          exact x.property⟩
      invFun := fun x =>
        ⟨fourSourceCycle.symm x.1, by
          change fourSourceAugmentation (fourSourceCycle.symm x.1) = 0
          rw [fourSourceAugmentation_cycle_symm]
          exact x.property⟩
      left_inv := fun x => by
        apply Subtype.ext
        exact fourSourceCycle.symm_apply_apply x.1
      right_inv := fun x => by
        apply Subtype.ext
        exact fourSourceCycle.apply_symm_apply x.1
      map_add' := fun x y => by
        apply Subtype.ext
        exact map_add fourSourceCycle x.1 y.1
      map_smul' := fun r x => by
        apply Subtype.ext
        exact map_smul fourSourceCycle r x.1 }
  norm_map' x := fourSourceCycle.norm_map x.1

@[simp]
theorem fourSourceAugmentationCycle_apply
    (x : FourSourceAugmentationSpace) (j : Fin 4) :
    (fourSourceAugmentationCycle x).1 j = x.1 (axisCycle.symm j) :=
  rfl

/-- Centered carrier vector attached to one intrinsic source-period class. -/
noncomputable def centeredSourceVector (i : Fin 4) :
    FourSourceAugmentationSpace :=
  ⟨WithLp.toLp 2 (centeredAtom 3 i), by
    change ∑ j, centeredAtom 3 i j = 0
    exact centeredAtom_component_sum 3 i⟩

/-- The source cycle on the linear carrier extends the intrinsic cyclic
permutation of centered source-period classes. -/
theorem fourSourceAugmentationCycle_centeredSourceVector
    (i : Fin 4) :
    fourSourceAugmentationCycle (centeredSourceVector i) =
      centeredSourceVector (axisCycle i) := by
  ext j
  change centeredAtom 3 i (axisCycle.symm j) =
    centeredAtom 3 (axisCycle i) j
  simpa using
    (centeredAtom_equivariant axisCycle i (axisCycle.symm j)).symm

/-- Intrinsic cyclic action on the complete raw-period quotient of positive
same-endpoint histories.  It is transported through the proved quotient
classification, not selected from microscopic representatives. -/
noncomputable def rawSourcePeriodClassCycle
    (L : ℕ) (hL : 4 ≤ L) :
    PositiveSameEndpointHistory.RawSourcePeriodClass L hL ≃
      PositiveSameEndpointHistory.RawSourcePeriodClass L hL :=
  ((rawSourcePeriodClassEquivAxis L hL).trans axisCycle).trans
    (rawSourcePeriodClassEquivAxis L hL).symm

/-- Under the intrinsic quotient classification, the class action is exactly
the four-source cycle. -/
theorem rawSourcePeriodClassCycle_firstAxis
    (L : ℕ) (hL : 4 ≤ L)
    (q : PositiveSameEndpointHistory.RawSourcePeriodClass L hL) :
    PositiveSameEndpointHistory.rawSourcePeriodClassFirstAxis
        (rawSourcePeriodClassCycle L hL q) =
      axisCycle
        (PositiveSameEndpointHistory.rawSourcePeriodClassFirstAxis q) := by
  change
    (rawSourcePeriodClassEquivAxis L hL)
        ((rawSourcePeriodClassEquivAxis L hL).symm
          (axisCycle ((rawSourcePeriodClassEquivAxis L hL) q))) =
      axisCycle ((rawSourcePeriodClassEquivAxis L hL) q)
  exact (rawSourcePeriodClassEquivAxis L hL).apply_symm_apply _

/-- Four source-cycle steps are the identity on the augmentation carrier. -/
theorem fourSourceAugmentationCycle_four :
    (fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[4] =
        id := by
  funext x
  ext j
  fin_cases j <;> rfl

/-- A concrete augmentation vector in the real `-1` eigendirection. -/
noncomputable def alternatingSourceVector : FourSourceAugmentationSpace :=
  ⟨WithLp.toLp 2 ![(1 : ℝ), -1, 1, -1], by
    simp [fourSourceAugmentation, Fin.sum_univ_succ]⟩

/-- A concrete augmentation vector in the quarter-turn plane. -/
noncomputable def transverseSourceVector : FourSourceAugmentationSpace :=
  ⟨WithLp.toLp 2 ![(1 : ℝ), 0, -1, 0], by
    simp [fourSourceAugmentation, Fin.sum_univ_succ]⟩

theorem fourSourceAugmentationCycle_alternating :
    fourSourceAugmentationCycle alternatingSourceVector =
      -alternatingSourceVector := by
  ext j
  fin_cases j <;>
    norm_num [fourSourceAugmentationCycle, fourSourceCycle,
      alternatingSourceVector, axisCycle, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.cons_val_fin_one]

theorem fourSourceAugmentationCycle_transverse_ne_self :
    fourSourceAugmentationCycle transverseSourceVector ≠
      transverseSourceVector := by
  intro h
  have h0 :=
    congrArg (fun x : FourSourceAugmentationSpace => x.1 (0 : Fin 4)) h
  norm_num [fourSourceAugmentationCycle, fourSourceCycle,
    transverseSourceVector, axisCycle, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_fin_one] at h0

theorem fourSourceAugmentationCycle_transverse_ne_neg :
    fourSourceAugmentationCycle transverseSourceVector ≠
      -transverseSourceVector := by
  intro h
  have h1 :=
    congrArg (fun x : FourSourceAugmentationSpace => x.1 (1 : Fin 4)) h
  norm_num [fourSourceAugmentationCycle, fourSourceCycle,
    transverseSourceVector, axisCycle, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_fin_one] at h1

theorem fourSourceAugmentationCycle_two_transverse :
    ((fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[2])
        transverseSourceVector =
      -transverseSourceVector := by
  ext j
  fin_cases j <;>
    norm_num [fourSourceAugmentationCycle, fourSourceCycle,
      transverseSourceVector, axisCycle, Function.iterate_succ_apply,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.cons_val_three, Matrix.cons_val_fin_one]

theorem alternatingSourceVector_ne_zero :
    alternatingSourceVector ≠ 0 := by
  intro h
  have h0 :=
    congrArg (fun x : FourSourceAugmentationSpace => x.1 (0 : Fin 4)) h
  norm_num [alternatingSourceVector] at h0

theorem transverseSourceVector_ne_zero :
    transverseSourceVector ≠ 0 := by
  intro h
  have h0 :=
    congrArg (fun x : FourSourceAugmentationSpace => x.1 (0 : Fin 4)) h
  norm_num [transverseSourceVector] at h0

/-- The source-generated action has exact order four: no positive smaller
iterate is the identity. -/
theorem fourSourceAugmentationCycle_exactOrderFour :
    (fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[4] = id ∧
    (fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[1] ≠ id ∧
    (fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[2] ≠ id ∧
    (fourSourceAugmentationCycle :
      FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[3] ≠ id := by
  refine ⟨fourSourceAugmentationCycle_four, ?_, ?_, ?_⟩
  · intro h
    have hx := congrFun h transverseSourceVector
    simpa using fourSourceAugmentationCycle_transverse_ne_self hx
  · intro h
    have hx := congrFun h transverseSourceVector
    rw [fourSourceAugmentationCycle_two_transverse] at hx
    have hx0 :=
      congrArg (fun x : FourSourceAugmentationSpace => x.1 (0 : Fin 4)) hx
    norm_num [transverseSourceVector] at hx0
  · intro hthree
    have hcomp := congrArg
      (fun f : FourSourceAugmentationSpace → FourSourceAugmentationSpace =>
        fourSourceAugmentationCycle ∘ f) hthree
    have hfour :
        (fourSourceAugmentationCycle :
          FourSourceAugmentationSpace → FourSourceAugmentationSpace)^[4] =
          fourSourceAugmentationCycle := by
      simpa [Function.iterate_succ_apply'] using hcomp
    rw [fourSourceAugmentationCycle_four] at hfour
    exact fourSourceAugmentationCycle_transverse_ne_self
      (congrFun hfour.symm transverseSourceVector)

/-- The source-generated order-four action is not a real scalar operator. -/
theorem fourSourceAugmentationCycle_nonScalar :
    ¬ ∃ r : ℝ, ∀ x : FourSourceAugmentationSpace,
      fourSourceAugmentationCycle x = r • x := by
  rintro ⟨r, hr⟩
  have halt := hr alternatingSourceVector
  rw [fourSourceAugmentationCycle_alternating] at halt
  have hcoord :=
    congrArg (fun x : FourSourceAugmentationSpace => x.1 (0 : Fin 4)) halt
  have hrneg : r = -1 := by
    change (-1 : ℝ) = r * 1 at hcoord
    linarith
  have htrans := hr transverseSourceVector
  rw [hrneg, neg_one_smul] at htrans
  exact fourSourceAugmentationCycle_transverse_ne_neg htrans

/-- The selected quarter-turn vector is orthogonal to its cyclic image. -/
theorem transverseSourceVector_inner_cycle :
    inner ℝ transverseSourceVector
      (fourSourceAugmentationCycle transverseSourceVector) = 0 := by
  change
    (∑ i : Fin 4,
      (![1, 0, -1, 0] : Fin 4 → ℝ) (axisCycle.symm i) *
        (![1, 0, -1, 0] : Fin 4 → ℝ) i) = 0
  norm_num [Fin.sum_univ_four, axisCycle, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.cons_val_fin_one]

/-- Cyclic reduced Noether datum generated by the concrete four-source
augmentation action. -/
noncomputable def fourSourceCyclicNoetherData :
    CyclicReducedHolonomyData FourSourceAugmentationSpace where
  hol := fourSourceAugmentationCycle
  period := 4
  period_pos := by norm_num
  period_closed := fourSourceAugmentationCycle_four

/-- The source-generated Noether charge is conserved around every cyclic
orbit and the orbit closes after four steps. -/
theorem fourSourceNoetherInvariant
    (x : FourSourceAugmentationSpace) (n : ℕ) :
    fourSourceCyclicNoetherData.toReducedHolonomyData.charge
          (fourSourceCyclicNoetherData.toReducedHolonomyData.orbitNat x n) =
        fourSourceCyclicNoetherData.toReducedHolonomyData.charge x ∧
      fourSourceCyclicNoetherData.toReducedHolonomyData.orbitNat x
          (n + 4) =
        fourSourceCyclicNoetherData.toReducedHolonomyData.orbitNat x n := by
  exact
    ⟨DiscreteNoether.finiteCyclicDiscreteNoetherChargeInvariant
        fourSourceCyclicNoetherData x n,
      DiscreteNoether.finiteCyclicDiscreteNoetherOrbitClosed
        fourSourceCyclicNoetherData x n⟩

/-- The order-four source-generated Noether charge is genuinely directional:
it cannot be a fixed scalar multiple of the squared norm on the whole
rank-three augmentation carrier. -/
theorem fourSourceNoetherCharge_not_scalar_norm :
    ¬ ∃ r : ℝ, ∀ x : FourSourceAugmentationSpace,
      fourSourceCyclicNoetherData.toReducedHolonomyData.charge x =
        r * ‖x‖ ^ 2 := by
  rintro ⟨r, hr⟩
  have halt := hr alternatingSourceVector
  have htrans := hr transverseSourceVector
  have haltCharge :
      fourSourceCyclicNoetherData.toReducedHolonomyData.charge
          alternatingSourceVector =
        2 * ‖alternatingSourceVector‖ ^ 2 := by
    unfold ReducedHolonomyData.charge reducedHolonomyCharge
    simp only [fourSourceCyclicNoetherData]
    rw [fourSourceAugmentationCycle_alternating]
    rw [sub_neg_eq_add, inner_add_right, real_inner_self_eq_norm_sq]
    ring
  have htransCharge :
      fourSourceCyclicNoetherData.toReducedHolonomyData.charge
          transverseSourceVector =
        ‖transverseSourceVector‖ ^ 2 := by
    unfold ReducedHolonomyData.charge reducedHolonomyCharge
    simp only [fourSourceCyclicNoetherData]
    rw [inner_sub_right, transverseSourceVector_inner_cycle,
      real_inner_self_eq_norm_sq]
    ring
  rw [haltCharge] at halt
  rw [htransCharge] at htrans
  have haltNorm : 0 < ‖alternatingSourceVector‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr alternatingSourceVector_ne_zero)
  have htransNorm : 0 < ‖transverseSourceVector‖ ^ 2 :=
    sq_pos_of_pos (norm_pos_iff.mpr transverseSourceVector_ne_zero)
  have hrTwo : r = 2 := by nlinarith
  have hrOne : r = 1 := by nlinarith
  linarith

end

end SourceNoether
end Hardtest
