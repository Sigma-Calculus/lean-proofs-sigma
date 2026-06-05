/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Mathlib

/-!
# Finite horizon readout separation

This file formalizes the finite operator-theoretic core used in Appendix VI for
Sigma horizon readout separation.  The namespace is deliberately paper-facing:
`SigmaProofs.HorizonReadout` contains the theorem-level statement that a
non-injective or thermal external readout of a projected channel is not, by
itself, internal information loss when the completed residual evolution is
unitary.
-/

namespace SigmaProofs.HorizonReadout

/--
Finite residual completion of a projected external channel.  The completed
residual evolution is represented by an equivalence, which is the finite-set
version of a unitary information-preserving evolution.
-/
structure FiniteResidualCompletion (Ext Comp : Type*) [Fintype Ext] [Fintype Comp] where
  completedEvolution : Comp ≃ Comp
  embedExternal : Ext → Comp
  projectExternal : Comp → Ext
  projectedChannel : Ext → Ext
  compression : ∀ x : Ext,
    projectExternal (completedEvolution (embedExternal x)) = projectedChannel x

namespace FiniteResidualCompletion

variable {Ext Comp Therm : Type*} [Fintype Ext] [Fintype Comp]

/-- The selected external thermodynamic readout after the projected channel. -/
def externalReadout (D : FiniteResidualCompletion Ext Comp) (readout : Ext → Therm) :
    Ext → Therm :=
  fun x => readout (D.projectedChannel x)

/-- Internal information loss means failure of injectivity of the completed evolution. -/
def InternalInformationLoss (D : FiniteResidualCompletion Ext Comp) : Prop :=
  ¬ Function.Injective D.completedEvolution

/-- External readout incompleteness means failure of injectivity of the selected readout. -/
def ExternalReadoutIncomplete (D : FiniteResidualCompletion Ext Comp)
    (readout : Ext → Therm) : Prop :=
  ¬ Function.Injective (D.externalReadout readout)

lemma completedEvolution_injective (D : FiniteResidualCompletion Ext Comp) :
    Function.Injective D.completedEvolution :=
  D.completedEvolution.injective

lemma completedEvolution_eq_iff (D : FiniteResidualCompletion Ext Comp)
    (x y : Comp) :
    D.completedEvolution x = D.completedEvolution y ↔ x = y := by
  constructor
  · intro h
    exact D.completedEvolution.injective h
  · intro h
    rw [h]

lemma no_internal_information_loss (D : FiniteResidualCompletion Ext Comp) :
    ¬ D.InternalInformationLoss := by
  intro hLoss
  exact hLoss D.completedEvolution_injective

lemma projectedChannel_as_compression (D : FiniteResidualCompletion Ext Comp)
    (x : Ext) :
    D.projectExternal (D.completedEvolution (D.embedExternal x)) =
      D.projectedChannel x :=
  D.compression x

lemma externalReadout_eq_compressed_readout
    (D : FiniteResidualCompletion Ext Comp) (readout : Ext → Therm)
    (x : Ext) :
    D.externalReadout readout x =
      readout (D.projectExternal (D.completedEvolution (D.embedExternal x))) := by
  rw [externalReadout, D.compression x]

lemma externalReadoutIncomplete_of_witness
    (D : FiniteResidualCompletion Ext Comp) (readout : Ext → Therm)
    {x y : Ext} (hxy : x ≠ y)
    (hread : D.externalReadout readout x = D.externalReadout readout y) :
    D.ExternalReadoutIncomplete readout := by
  intro hinj
  exact hxy (hinj hread)

/--
Readout separation: external readout incompleteness is compatible with an
information-preserving completed residual evolution.
-/
theorem finiteReadoutSeparation
    (D : FiniteResidualCompletion Ext Comp) (readout : Ext → Therm)
    (hincomplete : D.ExternalReadoutIncomplete readout) :
    ¬ D.InternalInformationLoss ∧ D.ExternalReadoutIncomplete readout :=
  ⟨D.no_internal_information_loss, hincomplete⟩

end FiniteResidualCompletion

/-- Finite horizon readout datum: a residual completion plus a chosen thermal readout. -/
structure FiniteHorizonReadoutDatum (Ext Comp Therm : Type*)
    [Fintype Ext] [Fintype Comp] where
  completion : FiniteResidualCompletion Ext Comp
  thermalReadout : Ext → Therm

namespace FiniteHorizonReadoutDatum

variable {Ext Comp Therm : Type*} [Fintype Ext] [Fintype Comp]

/-- The complete external horizon readout selected from the projected channel. -/
def externalReadout (D : FiniteHorizonReadoutDatum Ext Comp Therm) : Ext → Therm :=
  D.completion.externalReadout D.thermalReadout

/-- The completed residual evolution in a finite horizon datum is information-preserving. -/
lemma completedEvolution_injective (D : FiniteHorizonReadoutDatum Ext Comp Therm) :
    Function.Injective D.completion.completedEvolution :=
  D.completion.completedEvolution_injective

/--
The finite horizon readout separation theorem: a non-injective external thermal
readout does not imply internal information loss in the completed residual
dynamics.
-/
theorem finiteHorizonReadoutSeparation
    (D : FiniteHorizonReadoutDatum Ext Comp Therm)
    (hincomplete : ¬ Function.Injective D.externalReadout) :
    ¬ D.completion.InternalInformationLoss ∧ ¬ Function.Injective D.externalReadout :=
  ⟨D.completion.no_internal_information_loss, hincomplete⟩

end FiniteHorizonReadoutDatum

/-- A two-state completed horizon sector with identity completed evolution. -/
def twoStateCompletion : FiniteResidualCompletion Bool Bool where
  completedEvolution := Equiv.refl Bool
  embedExternal := id
  projectExternal := id
  projectedChannel := id
  compression := by
    intro x
    rfl

/-- A maximally coarse thermal readout of the two-state external sector. -/
def twoStateThermalReadout (_ : Bool) : PUnit :=
  PUnit.unit

lemma twoStateThermalReadout_noninjective :
    ¬ Function.Injective twoStateThermalReadout := by
  intro hinj
  have htf : true = false := hinj (by rfl)
  cases htf

/--
Concrete finite example: thermal readout can be incomplete while the completed
evolution is injective.
-/
theorem finiteThermalReadoutSeparationExample :
    ¬ twoStateCompletion.InternalInformationLoss ∧
      twoStateCompletion.ExternalReadoutIncomplete twoStateThermalReadout := by
  exact twoStateCompletion.finiteReadoutSeparation
    twoStateThermalReadout twoStateThermalReadout_noninjective

end SigmaProofs.HorizonReadout
