/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Mathlib

/-!
# Horizon-to-radiation visibility criterion

This file formalizes the theorem-level reconstruction criterion used after the
finite horizon readout separation layer.  It does not construct the physical
Sigma horizon-to-radiation map.  Instead, it proves the exact quotient statement
needed once such a map is supplied: if the radiation readout identifies exactly
the quotient-null horizon directions, then it induces an injective map from the
reduced horizon quotient into the radiation readout data.
-/

namespace SigmaProofs.HorizonRadiationVisibility

/--
A horizon-to-radiation visibility datum consists of a radiation readout from a
horizon carrier, a quotient-null equivalence relation on that carrier, and the
kernel-exactness statement that the readout identifies precisely quotient-null
pairs.
-/
structure HorizonRadiationVisibilityDatum (Horizon Radiation : Type*) where
  radiationReadout : Horizon → Radiation
  quotientNull : Setoid Horizon
  kernel_exact : ∀ x y : Horizon,
    radiationReadout x = radiationReadout y ↔ quotientNull.r x y

namespace HorizonRadiationVisibilityDatum

variable {Horizon Radiation : Type*}

/-- The reduced horizon quotient by quotient-null directions. -/
abbrev ReducedHorizon (D : HorizonRadiationVisibilityDatum Horizon Radiation) : Type _ :=
  Quotient D.quotientNull

/-- The radiation readout induced on the reduced horizon quotient. -/
def reducedRadiationReadout
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) :
    D.ReducedHorizon → Radiation :=
  Quotient.lift D.radiationReadout (fun x y hxy => (D.kernel_exact x y).mpr hxy)

lemma reducedRadiationReadout_mk
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) (x : Horizon) :
    D.reducedRadiationReadout (Quotient.mk D.quotientNull x) = D.radiationReadout x :=
  rfl

/-- Quotient-null equivalent horizon representatives have the same radiation readout. -/
lemma radiationReadout_eq_of_null
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) {x y : Horizon}
    (hxy : D.quotientNull.r x y) :
    D.radiationReadout x = D.radiationReadout y :=
  (D.kernel_exact x y).mpr hxy

/-- Equal radiation readout forces equality in the reduced horizon quotient. -/
lemma quotient_eq_of_radiationReadout_eq
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) {x y : Horizon}
    (hxy : D.radiationReadout x = D.radiationReadout y) :
    Quotient.mk D.quotientNull x = Quotient.mk D.quotientNull y :=
  Quotient.sound ((D.kernel_exact x y).mp hxy)

/-- The induced reduced readout is injective. -/
theorem reducedRadiationReadout_injective
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) :
    Function.Injective D.reducedRadiationReadout := by
  intro q₁ q₂ hq
  induction q₁ using Quotient.inductionOn with
  | h x =>
      induction q₂ using Quotient.inductionOn with
      | h y =>
          exact D.quotient_eq_of_radiationReadout_eq hq

/-- Equality of reduced radiation readouts is equivalent to equality in the quotient. -/
theorem reducedRadiationReadout_eq_iff
    (D : HorizonRadiationVisibilityDatum Horizon Radiation)
    (q₁ q₂ : D.ReducedHorizon) :
    D.reducedRadiationReadout q₁ = D.reducedRadiationReadout q₂ ↔ q₁ = q₂ := by
  constructor
  · intro hq
    exact D.reducedRadiationReadout_injective hq
  · intro hq
    rw [hq]

/-- The theorem-level information-completeness predicate for the reduced readout. -/
def InformationComplete
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) : Prop :=
  Function.Injective D.reducedRadiationReadout

/--
Horizon-to-radiation visibility criterion: kernel-exactness of the supplied
radiation readout makes the reduced horizon quotient information-complete in
the radiation readout data.
-/
theorem horizonRadiationVisibilityCriterion
    (D : HorizonRadiationVisibilityDatum Horizon Radiation) :
    D.InformationComplete :=
  D.reducedRadiationReadout_injective

end HorizonRadiationVisibilityDatum

/-- Equality as the quotient-null relation. -/
def equalitySetoid (α : Type*) : Setoid α where
  r := Eq
  iseqv := ⟨Eq.refl, Eq.symm, Eq.trans⟩

/-- A concrete exact two-state horizon-to-radiation visibility datum. -/
def twoStateExactVisibility : HorizonRadiationVisibilityDatum Bool Bool where
  radiationReadout := id
  quotientNull := equalitySetoid Bool
  kernel_exact := by
    intro x y
    exact Iff.rfl

/-- Concrete example: exact two-state visibility is information-complete. -/
theorem twoStateExactVisibility_informationComplete :
    twoStateExactVisibility.InformationComplete :=
  twoStateExactVisibility.horizonRadiationVisibilityCriterion

end SigmaProofs.HorizonRadiationVisibility
