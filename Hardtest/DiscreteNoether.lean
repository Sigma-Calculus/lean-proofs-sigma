/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.GaugeTransport

/-!
# Discrete Noether reduced holonomy formalization

This module provides the paper-facing Lean names for the finite reduced
holonomy Noether layer. The underlying closed kernel is imported from
`Hardtest.GaugeTransport`, where the gauge transport paper uses the same
finite reduced-holonomy structures. This module keeps the Noether paper's
formal verification surface separate and reusable for later downstream work.
-/

namespace Hardtest
namespace DiscreteNoether

open GaugeTransport.FiniteTransportComplex

variable {H Y Z W : Type*}
variable [NormedAddCommGroup H] [InnerProductSpace ℝ H]
variable [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]
variable [NormedAddCommGroup Z] [InnerProductSpace ℝ Z]
variable [NormedAddCommGroup W] [InnerProductSpace ℝ W]

/-- The reduced Noether charge is the reduced holonomy charge of the underlying
orthogonal holonomy datum. -/
noncomputable abbrev reducedNoetherCharge (X : ReducedHolonomyData H) (x : H) : ℝ :=
  X.charge x

/-- Paper-facing integer-orbit conservation of the reduced Noether charge. -/
theorem finiteDiscreteNoetherChargeIntegerOrbitInvariant
    (X : ReducedHolonomyData H) (x : H) (k : ℤ) :
    X.charge (X.orbitInt x k) = X.charge x :=
  finiteReducedHolonomyDataChargeIntegerOrbitInvariant X x k

/-- Paper-facing half squared step-length form of the reduced Noether charge. -/
theorem finiteDiscreteNoetherChargeHalfNormSq
    (X : ReducedHolonomyData H) (x : H) :
    X.charge x = (1 / 2 : ℝ) * ‖x - X.hol x‖ ^ 2 :=
  finiteReducedHolonomyDataChargeHalfNormSq X x

/-- Paper-facing nonnegativity of the reduced Noether charge. -/
theorem finiteDiscreteNoetherChargeNonnegative
    (X : ReducedHolonomyData H) (x : H) :
    0 ≤ X.charge x :=
  finiteReducedHolonomyDataChargeNonnegative X x

/-- Paper-facing zero-charge criterion for reduced Noether data. -/
theorem finiteDiscreteNoetherChargeZeroIffFixed
    (X : ReducedHolonomyData H) (x : H) :
    X.charge x = 0 ↔ X.hol x = x :=
  finiteReducedHolonomyDataChargeZeroIffFixed X x

/-- Paper-facing stationarity of the forward orbit at zero reduced Noether charge. -/
theorem finiteDiscreteNoetherZeroChargeOrbitConstant
    (X : ReducedHolonomyData H) (x : H) (hzero : X.charge x = 0) (n : ℕ) :
    X.orbitNat x n = x :=
  finiteReducedHolonomyDataZeroChargeOrbitConstant X x hzero n

/-- Paper-facing successor relation for the forward reduced Noether orbit. -/
theorem finiteDiscreteNoetherOrbitNatSucc
    (X : ReducedHolonomyData H) (x : H) (n : ℕ) :
    X.orbitNat x (n + 1) = X.hol (X.orbitNat x n) := by
  unfold ReducedHolonomyData.orbitNat
  rw [Function.iterate_succ_apply']

/-- Paper-facing half squared step-length form along a forward reduced Noether
orbit. -/
theorem finiteDiscreteNoetherChargeHalfNormSqOrbitStep
    (X : ReducedHolonomyData H) (x : H) (n : ℕ) :
    X.charge (X.orbitNat x n) =
      (1 / 2 : ℝ) * ‖X.orbitNat x n - X.orbitNat x (n + 1)‖ ^ 2 := by
  rw [finiteDiscreteNoetherChargeHalfNormSq X (X.orbitNat x n)]
  rw [← finiteDiscreteNoetherOrbitNatSucc X x n]

/-- Paper-facing bundled finite discrete Noether invariant for a reduced
orthogonal holonomy datum: charge conservation, half squared step-length form,
and nonnegativity along the forward orbit. -/
theorem finiteDiscreteNoetherModelIndependentInvariant
    (X : ReducedHolonomyData H) (x : H) (n : ℕ) :
    X.charge (X.orbitNat x n) = X.charge x ∧
      X.charge (X.orbitNat x n) =
        (1 / 2 : ℝ) * ‖X.orbitNat x n - X.orbitNat x (n + 1)‖ ^ 2 ∧
      0 ≤ X.charge (X.orbitNat x n) := by
  exact ⟨ReducedHolonomyData.charge_orbitNat X x n,
    finiteDiscreteNoetherChargeHalfNormSqOrbitStep X x n,
    finiteDiscreteNoetherChargeNonnegative X (X.orbitNat x n)⟩

/-- Paper-facing closure of cyclic reduced Noether orbits. -/
theorem finiteCyclicDiscreteNoetherOrbitClosed
    (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.orbitNat x (n + X.period) =
      X.toReducedHolonomyData.orbitNat x n :=
  finiteCyclicReducedHolonomyDataOrbitClosed X x n

/-- Paper-facing charge conservation on cyclic reduced Noether orbits. -/
theorem finiteCyclicDiscreteNoetherChargeInvariant
    (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.charge
      (X.toReducedHolonomyData.orbitNat x n) =
        X.toReducedHolonomyData.charge x :=
  finiteCyclicReducedHolonomyDataChargeInvariant X x n

/-- Paper-facing zero-charge criterion for cyclic reduced Noether data. -/
theorem finiteCyclicDiscreteNoetherChargeZeroIffFixed
    (X : CyclicReducedHolonomyData H) (x : H) :
    X.toReducedHolonomyData.charge x = 0 ↔
      X.toReducedHolonomyData.hol x = x :=
  finiteCyclicReducedHolonomyDataChargeZeroIffFixed X x

/-- Paper-facing stationarity of cyclic reduced Noether orbits at zero charge. -/
theorem finiteCyclicDiscreteNoetherZeroChargeOrbitConstant
    (X : CyclicReducedHolonomyData H) (x : H)
    (hzero : X.toReducedHolonomyData.charge x = 0) (n : ℕ) :
    X.toReducedHolonomyData.orbitNat x n = x :=
  finiteCyclicReducedHolonomyDataZeroChargeOrbitConstant X x hzero n

/-- Paper-facing bundled finite cyclic discrete Noether invariant matching the
model-independent theorem: charge conservation, half squared step-length form,
nonnegativity, and closure after the stored finite period. -/
theorem finiteCyclicDiscreteNoetherModelIndependentInvariant
    (X : CyclicReducedHolonomyData H) (x : H) (n : ℕ) :
    X.toReducedHolonomyData.charge
        (X.toReducedHolonomyData.orbitNat x n) =
      X.toReducedHolonomyData.charge x ∧
      X.toReducedHolonomyData.charge
          (X.toReducedHolonomyData.orbitNat x n) =
        (1 / 2 : ℝ) *
          ‖X.toReducedHolonomyData.orbitNat x n -
            X.toReducedHolonomyData.orbitNat x (n + 1)‖ ^ 2 ∧
      0 ≤ X.toReducedHolonomyData.charge
        (X.toReducedHolonomyData.orbitNat x n) ∧
      X.toReducedHolonomyData.orbitNat x (n + X.period) =
        X.toReducedHolonomyData.orbitNat x n := by
  exact ⟨finiteCyclicDiscreteNoetherChargeInvariant X x n,
    finiteDiscreteNoetherChargeHalfNormSqOrbitStep X.toReducedHolonomyData x n,
    finiteDiscreteNoetherChargeNonnegative X.toReducedHolonomyData
      (X.toReducedHolonomyData.orbitNat x n),
    finiteCyclicDiscreteNoetherOrbitClosed X x n⟩

/-- Paper-facing functoriality of reduced Noether charge under isometric
intertwiners. -/
theorem finiteDiscreteNoetherMorphismChargePreserving
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.charge (f.map x) = X.charge x :=
  finiteReducedHolonomyDataMorphismChargePreserving f x

/-- Paper-facing orbit intertwining under reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismOrbitIntertwining
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    f.map (X.orbitNat x n) = Ydata.orbitNat (f.map x) n :=
  finiteReducedHolonomyDataMorphismOrbitIntertwining f x n

/-- Paper-facing step-norm preservation under reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismStepNormPreserving
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    ‖f.map x - Ydata.hol (f.map x)‖ = ‖x - X.hol x‖ :=
  finiteReducedHolonomyDataMorphismStepNormPreserving f x

/-- Paper-facing mapped-orbit conservation under reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismMappedOrbitChargeConstant
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.charge (Ydata.orbitNat (f.map x) n) = X.charge x :=
  finiteReducedHolonomyDataMorphismMappedOrbitChargeConstant f x n

/-- Paper-facing identity morphism for reduced Noether data. -/
def finiteDiscreteNoetherIdentityMorphism
    (X : ReducedHolonomyData H) : ReducedHolonomyDataMorphism X X :=
  finiteReducedHolonomyDataIdentityMorphism X

/-- Paper-facing composition of reduced Noether morphisms. -/
def finiteDiscreteNoetherMorphismComp
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    {Zdata : ReducedHolonomyData Z}
    (g : ReducedHolonomyDataMorphism Ydata Zdata)
    (f : ReducedHolonomyDataMorphism X Ydata) :
    ReducedHolonomyDataMorphism X Zdata :=
  finiteReducedHolonomyDataMorphismComp g f

/-- Paper-facing left identity law for reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismLeftIdentityMap
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (ReducedHolonomyDataMorphism.comp
      (ReducedHolonomyDataMorphism.identity Ydata) f).map x = f.map x :=
  finiteReducedHolonomyDataMorphismLeftIdentityMap f x

/-- Paper-facing right identity law for reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismRightIdentityMap
    {X : ReducedHolonomyData H} {Ydata : ReducedHolonomyData Y}
    (f : ReducedHolonomyDataMorphism X Ydata) (x : H) :
    (ReducedHolonomyDataMorphism.comp f
      (ReducedHolonomyDataMorphism.identity X)).map x = f.map x :=
  finiteReducedHolonomyDataMorphismRightIdentityMap f x

/-- Paper-facing associativity law for reduced Noether morphisms. -/
theorem finiteDiscreteNoetherMorphismAssocMap
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
  finiteReducedHolonomyDataMorphismAssocMap h g f x

/-- Paper-facing charge preservation for cyclic reduced Noether morphisms. -/
theorem finiteCyclicDiscreteNoetherMorphismChargePreserving
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    Ydata.toReducedHolonomyData.charge (f.map x) =
      X.toReducedHolonomyData.charge x :=
  finiteCyclicReducedHolonomyDataMorphismChargePreserving f x

/-- Paper-facing mapped cyclic orbit conservation under cyclic reduced Noether
morphisms. -/
theorem finiteCyclicDiscreteNoetherMorphismMappedOrbitChargeConstant
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) (n : ℕ) :
    Ydata.toReducedHolonomyData.charge
      (Ydata.toReducedHolonomyData.orbitNat (f.map x) n) =
        X.toReducedHolonomyData.charge x :=
  finiteCyclicReducedHolonomyDataMorphismMappedOrbitChargeConstant f x n

/-- Paper-facing left identity law for cyclic reduced Noether morphisms. -/
theorem finiteCyclicDiscreteNoetherMorphismLeftIdentityMap
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (CyclicReducedHolonomyDataMorphism.comp
      (CyclicReducedHolonomyDataMorphism.identity Ydata) f).map x = f.map x :=
  finiteCyclicReducedHolonomyDataMorphismLeftIdentityMap f x

/-- Paper-facing right identity law for cyclic reduced Noether morphisms. -/
theorem finiteCyclicDiscreteNoetherMorphismRightIdentityMap
    {X : CyclicReducedHolonomyData H} {Ydata : CyclicReducedHolonomyData Y}
    (f : CyclicReducedHolonomyDataMorphism X Ydata) (x : H) :
    (CyclicReducedHolonomyDataMorphism.comp f
      (CyclicReducedHolonomyDataMorphism.identity X)).map x = f.map x :=
  finiteCyclicReducedHolonomyDataMorphismRightIdentityMap f x

/-- Paper-facing associativity law for cyclic reduced Noether morphisms. -/
theorem finiteCyclicDiscreteNoetherMorphismAssocMap
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
  finiteCyclicReducedHolonomyDataMorphismAssocMap h g f x

end DiscreteNoether
end Hardtest
