/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.GaugeTransport
import Hardtest.SigmaAxioms

/-!
# Finite source-balanced confluence certificates

This file formalizes the finite cellular core of a source-balanced confluence
argument.  It separates two levels:

* `parallelChannelCertificate` is an explicit finite model with `d + 1`
  parallel channels and centered source periods;
* `SigmaSourceConfluenceRealization` is the additional realization criterion
  required to register such channels as admissible Sigma transition histories;
* `ConcreteFourCoordinateModel` constructs that realization in rank three
  inside the finite four-coordinate Sigma dynamics.
* `SourcePeriodClass` quotients admissible same-endpoint histories by their
  complete registered source-period vectors and proves the corresponding
  universal readout factorization.
* `FiniteSourcePeriodCarrierRegistration` packages the finite class-level
  data needed by the simplex-carrier normal form without selecting microscopic
  path representatives.
* `RawAtomicSourceIncidenceCertificate` constructs the centered source
  cochain from a raw transition-chain incidence by augmentation projection.

The parallel-channel certificate alone does not instantiate the transition
criterion.  The concrete rank-three namespace does.

## TeX correspondence

The primary paper-facing source is `discrete_noether_sigma_v3.tex`, especially
the theorem titled "A source-balanced confluence certificate supplies the
ambient path rank" and its canonical parallel-channel corollary.  The resulting
rank certificate supports the local source-orbit and simplex-carrier route in
`Sigma_Finite_Line_Carrier_Tetrahedral_Stability_Criterion_full_proof.tex`.

The Lean development proves the centered augmentation algebra, the exact
rank-`d` statement, the finite parallel-channel certificate, the construction
of source-indexed Sigma histories from a cyclic equivariant history orbit, and
a concrete four-coordinate rank-three realization.  It proves that the
distinguished source-period classes retain the augmentation rank independently
of path representatives, and that their centered readout has the canonical
simplex Gram matrix.  It also proves the topology/source-defect alternative for
face fillings and constructs the maximal source-admissible face hull.  It does
not identify an independently prescribed physical transition network with the
concrete model.  On such a network the raw transition-chain source incidence,
its common-mode face balance, and the distinguished confluent histories remain
same-section realization data.
-/

namespace Hardtest
namespace SourceConfluence

open scoped BigOperators
open GaugeTransport
open GaugeTransport.FiniteTransportComplex

/-- The centered source coefficient for atom `i` in component `j`. -/
noncomputable def centeredAtom (d : ℕ) (i j : Fin (d + 1)) : ℝ :=
  (if i = j then 1 else 0) - 1 / (d + 1 : ℝ)

/-- The centered atoms sum to zero in every component. -/
theorem centeredAtom_sum (d : ℕ) (j : Fin (d + 1)) :
    ∑ i, centeredAtom d i j = 0 := by
  classical
  simp [centeredAtom, Finset.sum_sub_distrib]
  field_simp
  norm_num

/-- Every centered source atom lies in the augmentation-null subspace. -/
theorem centeredAtom_component_sum (d : ℕ) (i : Fin (d + 1)) :
    ∑ j, centeredAtom d i j = 0 := by
  simpa [centeredAtom, eq_comm] using centeredAtom_sum d i

/-- Evaluating a linear combination of centered atoms gives the coefficient in
that component minus the average coefficient. -/
theorem centeredAtom_combination_apply (d : ℕ) (a : Fin (d + 1) → ℝ)
    (j : Fin (d + 1)) :
    ∑ i, a i * centeredAtom d i j =
      a j - (∑ i, a i) / (d + 1 : ℝ) := by
  classical
  simp only [centeredAtom, mul_sub, Finset.sum_sub_distrib]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, one_div, sub_right_inj]
  have hsum :
      (∑ i, a i * (d + 1 : ℝ)⁻¹) =
        (∑ i, a i) * (d + 1 : ℝ)⁻¹ := by
    simpa only using
      (Finset.sum_mul Finset.univ a (d + 1 : ℝ)⁻¹).symm
  rw [hsum]
  rfl

/-- The all-ones relation is the only coefficient relation among the centered
atoms.  This is the finite coefficient-kernel form of the rank-`d`
augmentation certificate. -/
theorem centeredAtom_only_constant_relations (d : ℕ) (a : Fin (d + 1) → ℝ)
    (hzero : ∀ j, ∑ i, a i * centeredAtom d i j = 0) :
    ∀ i j, a i = a j := by
  intro i j
  have hi := hzero i
  have hj := hzero j
  rw [centeredAtom_combination_apply] at hi hj
  linarith

/-- Simultaneously permuting source atoms and components preserves the centered
source coefficients. -/
theorem centeredAtom_equivariant
    {d : ℕ} (p : Equiv.Perm (Fin (d + 1)))
    (i j : Fin (d + 1)) :
    centeredAtom d (p i) (p j) = centeredAtom d i j := by
  simp [centeredAtom, p.injective.eq_iff]

/-- Distinct source atoms have distinct centered coefficient vectors. -/
theorem centeredAtom_injective (d : ℕ) :
    Function.Injective (centeredAtom d) := by
  intro i k h
  by_contra hik
  have hi := congrFun h i
  simp [centeredAtom] at hi
  exact hik hi.symm

/-- Exact finite certificate that a family of `d + 1` vectors has one
coefficient relation, namely the constant relation. -/
def HasAugmentationRankCertificate (d : ℕ)
    (v : Fin (d + 1) → Fin (d + 1) → ℝ) : Prop :=
  (∀ j, ∑ i, v i j = 0) ∧
    ∀ a : Fin (d + 1) → ℝ,
      (∀ j, ∑ i, a i * v i j = 0) → ∀ i j, a i = a j

/-- The centered source family has the augmentation rank certificate. -/
theorem centeredAtom_hasAugmentationRankCertificate (d : ℕ) :
    HasAugmentationRankCertificate d (centeredAtom d) :=
  ⟨centeredAtom_sum d, centeredAtom_only_constant_relations d⟩

/-- The augmentation functional on the finite source-coordinate space. -/
noncomputable def augmentation (d : ℕ) :
    (Fin (d + 1) → ℝ) →ₗ[ℝ] ℝ where
  toFun x := ∑ i, x i
  map_add' x y := by simp [Finset.sum_add_distrib]
  map_smul' c x := by simp [Finset.mul_sum]

/-- The augmentation functional is nonzero in every finite rank. -/
theorem augmentation_ne_zero (d : ℕ) : augmentation d ≠ 0 := by
  intro h
  have hx := LinearMap.congr_fun h (fun _ : Fin (d + 1) => (1 : ℝ))
  simp [augmentation] at hx
  have hpos : (0 : ℝ) < d + 1 := by positivity
  linarith

/-- The augmentation-null source space has dimension `d`. -/
theorem augmentation_ker_finrank (d : ℕ) :
    Module.finrank ℝ (LinearMap.ker (augmentation d)) = d := by
  have h :=
    Module.Dual.finrank_ker_add_one_of_ne_zero (augmentation_ne_zero d)
  simp only [Module.finrank_fin_fun] at h
  omega

/-- The centered atoms span exactly the augmentation-null source space. -/
theorem centered_span_eq_augmentation_ker (d : ℕ) :
    Submodule.span ℝ (Set.range (centeredAtom d)) =
      LinearMap.ker (augmentation d) := by
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro v ⟨i, rfl⟩
    change ∑ j, centeredAtom d i j = 0
    simpa [centeredAtom, eq_comm] using centeredAtom_sum d i
  · intro x hx
    change (∑ i, x i) = 0 at hx
    have hrepr : x = ∑ i, x i • centeredAtom d i := by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      rw [centeredAtom_combination_apply, hx]
      simp
    rw [hrepr]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))

/-- The centered source family has literal linear span dimension `d`. -/
theorem centered_span_finrank (d : ℕ) :
    Module.finrank ℝ (Submodule.span ℝ (Set.range (centeredAtom d))) = d := by
  rw [centered_span_eq_augmentation_ker]
  exact augmentation_ker_finrank d

/-- The Gram matrix of the centered source atoms is the centered projection
matrix itself. -/
theorem centeredAtom_gram (d : ℕ) (i k : Fin (d + 1)) :
    ∑ j, centeredAtom d i j * centeredAtom d k j =
      centeredAtom d i k := by
  calc
    ∑ j, centeredAtom d i j * centeredAtom d k j =
        ∑ j, centeredAtom d i j * centeredAtom d j k := by
          apply Finset.sum_congr rfl
          intro j _
          congr 1
          simp [centeredAtom, eq_comm]
    _ = centeredAtom d i k -
        (∑ j, centeredAtom d i j) / (d + 1 : ℝ) :=
      centeredAtom_combination_apply d (centeredAtom d i) k
    _ = centeredAtom d i k := by
      rw [centeredAtom_component_sum]
      simp

/-- A finite payload sufficient to register distinguished source-period
classes at the carrier layer.  It records classes and their complete readout,
but does not require a preferred microscopic path representative. -/
structure FiniteSourcePeriodCarrierRegistration (d : ℕ) where
  Carrier : Type*
  distinguished : Fin (d + 1) → Carrier
  readout : Carrier → Fin (d + 1) → ℝ
  commonOffset : Fin (d + 1) → ℝ
  readout_distinguished :
    ∀ i j,
      readout (distinguished i) j =
        commonOffset j + centeredAtom d i j

namespace FiniteSourcePeriodCarrierRegistration

variable {d : ℕ}

/-- The centered readout of the distinguished period classes. -/
def centeredReadout (R : FiniteSourcePeriodCarrierRegistration d) :
    Fin (d + 1) → Fin (d + 1) → ℝ :=
  fun i j => R.readout (R.distinguished i) j - R.commonOffset j

/-- Centering the registered readout recovers the canonical augmentation
atoms exactly. -/
theorem centeredReadout_eq_centeredAtom
    (R : FiniteSourcePeriodCarrierRegistration d) :
    R.centeredReadout = centeredAtom d := by
  funext i j
  simp only [centeredReadout]
  rw [R.readout_distinguished]
  ring

/-- Distinguished period classes are pairwise distinct. -/
theorem distinguished_injective
    (R : FiniteSourcePeriodCarrierRegistration d) :
    Function.Injective R.distinguished := by
  intro i k h
  apply centeredAtom_injective d
  have hreadout : R.readout (R.distinguished i) =
      R.readout (R.distinguished k) :=
    congrArg R.readout h
  funext j
  have hj := congrFun hreadout j
  rw [R.readout_distinguished, R.readout_distinguished] at hj
  linarith

/-- The finite registration carries the exact augmentation rank
certificate. -/
theorem hasAugmentationRankCertificate
    (R : FiniteSourcePeriodCarrierRegistration d) :
    HasAugmentationRankCertificate d R.centeredReadout := by
  rw [R.centeredReadout_eq_centeredAtom]
  exact centeredAtom_hasAugmentationRankCertificate d

/-- The centered registration spans a carrier of dimension `d`. -/
theorem centeredSpan_finrank
    (R : FiniteSourcePeriodCarrierRegistration d) :
    Module.finrank ℝ
      (Submodule.span ℝ (Set.range R.centeredReadout)) = d := by
  rw [R.centeredReadout_eq_centeredAtom]
  exact centered_span_finrank d

/-- The centered registration has the regular-simplex Gram matrix before
normalization. -/
theorem centeredReadout_gram
    (R : FiniteSourcePeriodCarrierRegistration d)
    (i k : Fin (d + 1)) :
    ∑ j, R.centeredReadout i j * R.centeredReadout k j =
      centeredAtom d i k := by
  rw [R.centeredReadout_eq_centeredAtom]
  exact centeredAtom_gram d i k

end FiniteSourcePeriodCarrierRegistration

/-- Two vertices suffice for the canonical parallel-channel model. -/
abbrev ParallelVertex := Bool

/-- The `d + 1` source atoms label parallel edges. -/
abbrev ParallelEdge (d : ℕ) := Fin (d + 1)

/-- The canonical model has no two-cells; closedness is therefore exact and
vacuous rather than imported from a geometric face relation. -/
abbrev ParallelFace := Empty

/-- The canonical finite complex of `d + 1` parallel source channels. -/
def parallelChannelComplex (d : ℕ) :
    FiniteTransportComplex ParallelVertex (ParallelEdge d) ParallelFace where
  source := fun _ => false
  target := fun _ => true
  faceBoundary := fun f => nomatch f

/-- The path associated with a source atom is its single parallel edge. -/
def parallelChannelPath {d : ℕ} (i : ParallelEdge d) : List (ParallelEdge d) :=
  [i]

/-- Every canonical channel is a path from the common source to the common
target. -/
theorem parallelChannelPath_valid {d : ℕ} (i : ParallelEdge d) :
    (parallelChannelComplex d).IsEdgePathFrom false (parallelChannelPath i) true := by
  simp [parallelChannelComplex, parallelChannelPath, IsEdgePathFrom]

/-- Component `j` of the centered vector-valued source cochain. -/
noncomputable def parallelSourceCochain
    (d : ℕ) (j : Fin (d + 1)) : ParallelEdge d → ℝ :=
  fun i => centeredAtom d i j

/-- Each source component is a closed cellular cochain in the canonical finite
model. -/
theorem parallelSourceCochain_closed (d : ℕ) (j : Fin (d + 1)) :
    (parallelChannelComplex d).IsClosed1Cochain (parallelSourceCochain d j) := by
  funext f
  exact Empty.elim f

/-- The period of a centered source component along channel `i` is the
corresponding centered atom coefficient. -/
theorem parallelSourceCochain_period (d : ℕ) (i j : Fin (d + 1)) :
    pathIntegral (parallelSourceCochain d j) (parallelChannelPath i) =
      centeredAtom d i j := by
  simp [parallelSourceCochain, parallelChannelPath, pathIntegral]

/-- A finite source-balanced confluence certificate on a transport complex. -/
structure SourceBalancedConfluenceCertificate (d : ℕ)
    (V E F : Type*) [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  startVertex : V
  finishVertex : V
  path : Fin (d + 1) → List E
  pathValid :
    ∀ i, complex.IsEdgePathFrom startVertex (path i) finishVertex
  sourceCochain : Fin (d + 1) → E → ℝ
  sourceClosed :
    ∀ j, complex.IsClosed1Cochain (sourceCochain j)
  commonOffset : Fin (d + 1) → ℝ
  pathValue :
    ∀ i j,
      pathIntegral (sourceCochain j) (path i) =
        commonOffset j + centeredAtom d i j

namespace SourceBalancedConfluenceCertificate

variable {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]

/-- The admissible paths between the registered common endpoints of a
source-balanced confluence certificate. -/
def SameEndpointPath
    (C : SourceBalancedConfluenceCertificate d V E F) :=
  {p : List E // C.complex.IsEdgePathFrom C.startVertex p C.finishVertex}

/-- The complete source-period vector of an admissible same-endpoint path. -/
def sourcePeriodVector
    (C : SourceBalancedConfluenceCertificate d V E F)
    (p : C.SameEndpointPath) : Fin (d + 1) → ℝ :=
  fun j => pathIntegral (C.sourceCochain j) p.1

/-- Two admissible same-endpoint paths are physically indistinguishable at
the source-period layer precisely when all registered source periods agree. -/
def SameSourcePeriod
    (C : SourceBalancedConfluenceCertificate d V E F)
    (p p' : C.SameEndpointPath) : Prop :=
  C.sourcePeriodVector p = C.sourcePeriodVector p'

/-- Equality of complete source-period vectors is an equivalence relation on
admissible same-endpoint paths. -/
theorem sameSourcePeriod_equivalence
    (C : SourceBalancedConfluenceCertificate d V E F) :
    Equivalence C.SameSourcePeriod := by
  constructor
  · intro p
    rfl
  · intro p p' h
    exact h.symm
  · intro p p' p'' h h'
    exact h.trans h'

/-- The canonical source-period equivalence relation on admissible
same-endpoint paths. -/
def sourcePeriodSetoid
    (C : SourceBalancedConfluenceCertificate d V E F) :
    Setoid C.SameEndpointPath where
  r := C.SameSourcePeriod
  iseqv := C.sameSourcePeriod_equivalence

/-- A source-period class retains exactly the information visible to all
registered source components and discards the choice of path representative. -/
abbrev SourcePeriodClass
    (C : SourceBalancedConfluenceCertificate d V E F) :=
  Quotient C.sourcePeriodSetoid

/-- The source-period vector descends canonically to source-period classes. -/
def sourcePeriodClassReadout
    (C : SourceBalancedConfluenceCertificate d V E F) :
    C.SourcePeriodClass → Fin (d + 1) → ℝ :=
  Quotient.lift C.sourcePeriodVector (by
    intro p p' h
    exact h)

/-- Complete source periods separate the quotient classes by construction. -/
theorem sourcePeriodClassReadout_injective
    (C : SourceBalancedConfluenceCertificate d V E F) :
    Function.Injective C.sourcePeriodClassReadout := by
  intro q q' h
  revert h
  refine Quotient.inductionOn q ?_
  intro p
  refine Quotient.inductionOn q' ?_
  intro p' h'
  apply Quotient.sound
  exact h'

/-- Any same-endpoint path observable constant on source-period fibers factors
canonically through the source-period quotient. -/
def sourcePeriodQuotientLift
    (C : SourceBalancedConfluenceCertificate d V E F)
    {A : Sort*}
    (f : C.SameEndpointPath → A)
    (hf : ∀ p p', C.SameSourcePeriod p p' → f p = f p') :
    C.SourcePeriodClass → A :=
  Quotient.lift f hf

/-- The quotient lift evaluates to the original observable on every path
representative. -/
theorem sourcePeriodQuotientLift_mk
    (C : SourceBalancedConfluenceCertificate d V E F)
    {A : Sort*}
    (f : C.SameEndpointPath → A)
    (hf : ∀ p p', C.SameSourcePeriod p p' → f p = f p')
    (p : C.SameEndpointPath) :
    C.sourcePeriodQuotientLift f hf (Quotient.mk _ p) = f p :=
  rfl

/-- The quotient lift is the unique map whose pullback is the supplied
source-period-invariant observable. -/
theorem sourcePeriodQuotientLift_unique
    (C : SourceBalancedConfluenceCertificate d V E F)
    {A : Sort*}
    (f : C.SameEndpointPath → A)
    (hf : ∀ p p', C.SameSourcePeriod p p' → f p = f p')
    (g : C.SourcePeriodClass → A)
    (hg : ∀ p, g (Quotient.mk _ p) = f p) :
    g = C.sourcePeriodQuotientLift f hf := by
  funext q
  refine Quotient.inductionOn q ?_
  intro p
  rw [hg]
  rfl

/-- The source-indexed history supplied by a confluence certificate, regarded
as an admissible same-endpoint path. -/
def registeredSameEndpointPath
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i : Fin (d + 1)) : C.SameEndpointPath :=
  ⟨C.path i, C.pathValid i⟩

/-- The canonical source-period class of a registered source history. -/
def registeredSourcePeriodClass
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i : Fin (d + 1)) : C.SourcePeriodClass :=
  Quotient.mk _ (C.registeredSameEndpointPath i)

/-- Reading a registered source-history class recovers its common offset plus
the corresponding centered source atom. -/
theorem sourcePeriodClassReadout_registered
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i j : Fin (d + 1)) :
    C.sourcePeriodClassReadout (C.registeredSourcePeriodClass i) j =
      C.commonOffset j + centeredAtom d i j := by
  exact C.pathValue i j

/-- Removing the common offset from the quotient readout recovers the centered
source atom exactly. -/
theorem registeredSourcePeriodClass_centeredReadout
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i j : Fin (d + 1)) :
    C.sourcePeriodClassReadout (C.registeredSourcePeriodClass i) j -
        C.commonOffset j =
      centeredAtom d i j := by
  rw [C.sourcePeriodClassReadout_registered]
  ring

/-- The distinguished source-period classes retain the exact augmentation
rank certificate independently of their path representatives. -/
theorem registeredSourcePeriodClass_hasAugmentationRankCertificate
    (C : SourceBalancedConfluenceCertificate d V E F) :
    HasAugmentationRankCertificate d
      (fun i j =>
        C.sourcePeriodClassReadout (C.registeredSourcePeriodClass i) j -
          C.commonOffset j) := by
  simpa [C.registeredSourcePeriodClass_centeredReadout] using
    centeredAtom_hasAugmentationRankCertificate d

/-- Distinct source atoms determine distinct source-period classes even when
their path representatives are not unique. -/
theorem registeredSourcePeriodClass_injective
    (C : SourceBalancedConfluenceCertificate d V E F) :
    Function.Injective C.registeredSourcePeriodClass := by
  intro i k h
  apply centeredAtom_injective d
  funext j
  have hj :=
    congrFun (congrArg C.sourcePeriodClassReadout h) j
  rw [C.sourcePeriodClassReadout_registered,
    C.sourcePeriodClassReadout_registered] at hj
  linarith

/-- Every source-balanced confluence certificate canonically supplies the
finite carrier-registration payload on its source-period quotient. -/
def finiteSourcePeriodCarrierRegistration
    (C : SourceBalancedConfluenceCertificate d V E F) :
    FiniteSourcePeriodCarrierRegistration d where
  Carrier := C.SourcePeriodClass
  distinguished := C.registeredSourcePeriodClass
  readout := C.sourcePeriodClassReadout
  commonOffset := C.commonOffset
  readout_distinguished := C.sourcePeriodClassReadout_registered

/-- The signed comparison loop formed by a source-indexed path followed by
the reverse of a second source-indexed path with the same endpoints. -/
def comparisonLoop
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i k : Fin (d + 1)) : List (SignedEdgeStep E) :=
  signedForwardPath (C.path i) ++ signedReversePath (C.path k)

/-- A comparison of two source-indexed paths is a closed signed loop based at
their common initial vertex. -/
theorem comparisonLoop_isClosed
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i k : Fin (d + 1)) :
    C.complex.IsClosedSignedLoop C.startVertex (C.comparisonLoop i k) := by
  exact isSignedPathFrom_append C.complex
    (signedForwardPath_valid C.complex (C.pathValid i))
    (signedReversePath_valid C.complex (C.pathValid k))

/-- Integration over a comparison loop is the difference of the two ordinary
path integrals. -/
theorem comparisonLoop_integral
    (C : SourceBalancedConfluenceCertificate d V E F)
    (sigma : E → ℝ) (i k : Fin (d + 1)) :
    signedPathIntegral sigma (C.comparisonLoop i k) =
      pathIntegral sigma (C.path i) - pathIntegral sigma (C.path k) := by
  simp [comparisonLoop, signedPathIntegral_append,
    signedPathIntegral_forwardPath, signedPathIntegral_reversePath,
    sub_eq_add_neg]

/-- The source period of a comparison loop is the exact difference of the two
centered source atoms; the common offset cancels. -/
theorem comparisonLoop_sourcePeriod
    (C : SourceBalancedConfluenceCertificate d V E F)
    (i k j : Fin (d + 1)) :
    signedPathIntegral (C.sourceCochain j) (C.comparisonLoop i k) =
      centeredAtom d i j - centeredAtom d k j := by
  rw [C.comparisonLoop_integral, C.pathValue, C.pathValue]
  ring

/-- Distinct source histories determine a comparison loop which cannot bound a
finite 2-chain while the source marking remains a closed cochain.  Thus source
confluence forces a genuine first-homology carrier rather than a completely
face-filled path comparison. -/
theorem comparisonLoop_not_boundsBy2Chain
    (C : SourceBalancedConfluenceCertificate d V E F)
    {i k : Fin (d + 1)} (hik : i ≠ k) :
    ¬ SignedPathBoundsBy2Chain C.complex (C.comparisonLoop i k) := by
  intro hbounds
  have hzero :=
    signedPathIntegral_eq_zero_of_boundsBy2Chain_of_closed
      C.complex (C.sourceCochain i) (C.comparisonLoop i k)
      hbounds (C.sourceClosed i)
  have hperiod := C.comparisonLoop_sourcePeriod i k i
  have hone :
      centeredAtom d i i - centeredAtom d k i = 1 := by
    simp [centeredAtom, Ne.symm hik]
  linarith

/-- Removing the common offset from the path values recovers the centered
source family exactly. -/
theorem centeredPeriod (C : SourceBalancedConfluenceCertificate d V E F)
    (i j : Fin (d + 1)) :
    pathIntegral (C.sourceCochain j) (C.path i) - C.commonOffset j =
      centeredAtom d i j := by
  rw [C.pathValue]
  ring

/-- Every source-balanced confluence certificate carries the exact
augmentation rank certificate after removal of its common offset. -/
theorem hasAugmentationRankCertificate
    (C : SourceBalancedConfluenceCertificate d V E F) :
    HasAugmentationRankCertificate d
      (fun i j =>
        pathIntegral (C.sourceCochain j) (C.path i) - C.commonOffset j) := by
  simpa [C.centeredPeriod] using centeredAtom_hasAugmentationRankCertificate d

end SourceBalancedConfluenceCertificate

/-- A face is source-admissible precisely when every supplied source component
has zero cellular coboundary on that face. -/
def SourceAdmissibleFace
    {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (q : Fin (d + 1) → E → ℝ) :=
  {f : F // ∀ j, K.faceCoboundary (q j) f = 0}

noncomputable instance sourceAdmissibleFaceFintype
    {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (q : Fin (d + 1) → E → ℝ) :
    Fintype (SourceAdmissibleFace K q) := by
  classical
  refine Fintype.ofFinset
    (Finset.univ.filter fun f => ∀ j, K.faceCoboundary (q j) f = 0) ?_
  intro f
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  change
    (∀ j, K.faceCoboundary (q j) f = 0) ↔
      (∀ j, K.faceCoboundary (q j) f = 0)
  rfl

/-- The maximal source-admissible face hull keeps the vertex and edge section
fixed and retains exactly the candidate faces on which all source components
are closed. -/
noncomputable def sourceAdmissibleFaceHull
    {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (q : Fin (d + 1) → E → ℝ) :
    FiniteTransportComplex V E (SourceAdmissibleFace K q) := by
  classical
  exact
    { source := K.source
      target := K.target
      faceBoundary := fun f => K.faceBoundary f.1 }

/-- Every source component is closed on the source-admissible face hull. -/
theorem sourceAdmissibleFaceHull_closed
    {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (q : Fin (d + 1) → E → ℝ) (j : Fin (d + 1)) :
    (sourceAdmissibleFaceHull K q).IsClosed1Cochain (q j) := by
  classical
  funext f
  exact f.property j

/-- Every candidate face satisfying source closedness has a canonical inclusion
in the source-admissible face hull. -/
def sourceAdmissibleFaceHull_include
    {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (q : Fin (d + 1) → E → ℝ)
    (f : F) (hf : ∀ j, K.faceCoboundary (q j) f = 0) :
    SourceAdmissibleFace K q :=
  ⟨f, hf⟩

/-- Path integration commutes with a finite linear combination of edge
cochains. -/
theorem pathIntegral_finite_linearCombination
    {I E : Type*} [Fintype I]
    (a : I → ℝ) (q : I → E → ℝ) (edges : List E) :
    pathIntegral (fun e => ∑ i, a i * q i e) edges =
      ∑ i, a i * pathIntegral (q i) edges := by
  induction edges with
  | nil =>
      simp [pathIntegral]
  | cons e rest ih =>
      simp only [pathIntegral, ih]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      ring

/-- Cellular coboundary commutes with a finite linear combination of edge
cochains. -/
theorem faceCoboundary_finite_linearCombination
    {I V E F : Type*} [Fintype I] [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F)
    (a : I → ℝ) (q : I → E → ℝ) (f : F) :
    K.faceCoboundary (fun e => ∑ i, a i * q i e) f =
      ∑ i, a i * K.faceCoboundary (q i) f := by
  simp only [faceCoboundary, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro e _
  ring

/-- A theorem-level raw atomic source incidence on a finite transition
complex.  Its face flux may contain a common source mode, while its
distinguished path periods differ by the canonical source atoms.

This structure corresponds to the raw source-incidence criterion in
`discrete_noether_sigma_v3.tex`.  The augmentation projection below removes
the common mode and constructs the centered source cochain used by the
source-confluence theorem. -/
structure RawAtomicSourceIncidenceCertificate (d : ℕ)
    (V E F : Type*) [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  startVertex : V
  finishVertex : V
  path : Fin (d + 1) → List E
  pathValid :
    ∀ i, complex.IsEdgePathFrom startVertex (path i) finishVertex
  rawSource : Fin (d + 1) → E → ℝ
  rawFaceCommonMode :
    ∀ f, ∃ c : ℝ, ∀ j, complex.faceCoboundary (rawSource j) f = c
  rawOffset : Fin (d + 1) → ℝ
  rawPathValue :
    ∀ i j,
      pathIntegral (rawSource j) (path i) =
        rawOffset j + if i = j then 1 else 0

namespace RawAtomicSourceIncidenceCertificate

variable {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]

/-- The augmentation-projected source cochain. -/
noncomputable def projectedSourceCochain
    (C : RawAtomicSourceIncidenceCertificate d V E F)
    (j : Fin (d + 1)) : E → ℝ :=
  fun e => ∑ i, centeredAtom d i j * C.rawSource i e

/-- The common offset after augmentation projection. -/
noncomputable def projectedOffset
    (C : RawAtomicSourceIncidenceCertificate d V E F)
    (j : Fin (d + 1)) : ℝ :=
  ∑ i, C.rawOffset i * centeredAtom d i j

/-- Common-mode raw face flux is annihilated by the augmentation projection,
so every projected source component is a closed cellular cochain. -/
theorem projectedSourceCochain_closed
    (C : RawAtomicSourceIncidenceCertificate d V E F)
    (j : Fin (d + 1)) :
    C.complex.IsClosed1Cochain (C.projectedSourceCochain j) := by
  funext f
  change
    C.complex.faceCoboundary
      (fun e => ∑ i, centeredAtom d i j * C.rawSource i e) f = 0
  rw [faceCoboundary_finite_linearCombination]
  rcases C.rawFaceCommonMode f with ⟨c, hc⟩
  simp_rw [hc]
  rw [← Finset.sum_mul, centeredAtom_sum]
  simp

/-- Projecting the raw atomic path periods gives the exact centered source
periods required by the source-confluence certificate. -/
theorem projectedSourceCochain_pathValue
    (C : RawAtomicSourceIncidenceCertificate d V E F)
    (i j : Fin (d + 1)) :
    pathIntegral (C.projectedSourceCochain j) (C.path i) =
      C.projectedOffset j + centeredAtom d i j := by
  change
    pathIntegral
      (fun e => ∑ k, centeredAtom d k j * C.rawSource k e) (C.path i) =
        (∑ k, C.rawOffset k * centeredAtom d k j) +
          centeredAtom d i j
  rw [pathIntegral_finite_linearCombination]
  simp_rw [C.rawPathValue]
  have hdelta :
      (∑ k : Fin (d + 1),
        if i = k then centeredAtom d k j else 0) =
        centeredAtom d i j := by
    simp
  rw [← hdelta, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hik : i = k
  · simp [hik]
    ring
  · simp [hik]
    ring

/-- Augmentation projection turns raw atomic source incidence into the finite
source-balanced confluence certificate used by the period-class and simplex
carrier theorems. -/
noncomputable def toSourceBalancedConfluenceCertificate
    (C : RawAtomicSourceIncidenceCertificate d V E F) :
    SourceBalancedConfluenceCertificate d V E F where
  complex := C.complex
  startVertex := C.startVertex
  finishVertex := C.finishVertex
  path := C.path
  pathValid := C.pathValid
  sourceCochain := C.projectedSourceCochain
  sourceClosed := C.projectedSourceCochain_closed
  commonOffset := C.projectedOffset
  pathValue := C.projectedSourceCochain_pathValue

end RawAtomicSourceIncidenceCertificate

/-- The canonical parallel-channel model is an explicit finite
source-balanced confluence certificate. -/
noncomputable def parallelChannelCertificate (d : ℕ) :
    SourceBalancedConfluenceCertificate d ParallelVertex
      (ParallelEdge d) ParallelFace where
  complex := parallelChannelComplex d
  startVertex := false
  finishVertex := true
  path := parallelChannelPath
  pathValid := parallelChannelPath_valid
  sourceCochain := parallelSourceCochain d
  sourceClosed := parallelSourceCochain_closed d
  commonOffset := 0
  pathValue := by
    intro i j
    simp [parallelSourceCochain_period]

/-- The one-skeleton used only to type finite histories of actual
`SigmaFineEdge4` transitions.  Its empty face type does not provide a
cohomological closure claim. -/
def sigmaTransitionSkeleton (L : ℕ) :
    FiniteTransportComplex (SigmaCoord4 L) (SigmaFineEdge4 L) Empty where
  source := sigmaFineEdgeSource
  target := sigmaFineEdgeTarget
  faceBoundary := fun f => nomatch f

/-- A nonempty finite history of actual Sigma transitions with declared
endpoints and verified edge adjacency. -/
structure SigmaTransitionHistory4 (L : ℕ) where
  startVertex : SigmaCoord4 L
  finishVertex : SigmaCoord4 L
  edges : List (SigmaFineEdge4 L)
  nonempty : edges ≠ []
  pathValid :
    (sigmaTransitionSkeleton L).IsEdgePathFrom startVertex edges finishVertex

/-- A nonempty path of positive-tension Sigma transitions has strictly
increasing event time between its endpoints. -/
theorem positiveSigmaPath_eventTime_strict
    {L : ℕ} {hL : 4 ≤ L} (D : SigmaAdmissibleDynamics4 L hL)
    {startVertex finishVertex : SigmaCoord4 L}
    {edges : List (SigmaFineEdge4 L)}
    (hpath :
      (sigmaTransitionSkeleton L).IsEdgePathFrom
        startVertex edges finishVertex)
    (hnonempty : edges ≠ [])
    (hpositive : ∀ e, e ∈ edges → 0 < D.tension e) :
    D.eventTime startVertex < D.eventTime finishVertex := by
  induction edges generalizing startVertex with
  | nil =>
      exact False.elim (hnonempty rfl)
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      have hedgePositive := hpositive e (by simp)
      rw [D.tension_eq_time_div_scale e] at hedgePositive
      have hedge :
          D.eventTime (sigmaFineEdgeSource e) <
            D.eventTime (sigmaFineEdgeTarget e) :=
        sub_pos.mp
          ((div_pos_iff_of_pos_right (D.localScale_pos e)).mp hedgePositive)
      have hedgeFromStart :
          D.eventTime startVertex <
            D.eventTime (sigmaFineEdgeTarget e) := by
        change sigmaFineEdgeSource e = startVertex at hsource
        rw [← hsource]
        exact hedge
      by_cases hrest : rest = []
      · subst rest
        change finishVertex = sigmaFineEdgeTarget e at htail
        simpa [htail] using hedgeFromStart
      · have htailPositive :
            ∀ f, f ∈ rest → 0 < D.tension f := by
          intro f hf
          exact hpositive f (by simp [hf])
        exact lt_trans hedgeFromStart (ih htail hrest htailPositive)

/-- An automorphism of the finite Sigma transition skeleton that preserves the
admissible dynamics tension.  It acts on whole histories rather than replacing
them by single primitive edges. -/
structure SigmaTransitionAutomorphism4
    (L : ℕ) {hL : 4 ≤ L} (D : SigmaAdmissibleDynamics4 L hL) where
  vertexEquiv : Equiv.Perm (SigmaCoord4 L)
  edgeEquiv : Equiv.Perm (SigmaFineEdge4 L)
  source_map :
    ∀ e, sigmaFineEdgeSource (edgeEquiv e) =
      vertexEquiv (sigmaFineEdgeSource e)
  target_map :
    ∀ e, sigmaFineEdgeTarget (edgeEquiv e) =
      vertexEquiv (sigmaFineEdgeTarget e)
  tension_map :
    ∀ e, D.tension (edgeEquiv e) = D.tension e

namespace SigmaTransitionAutomorphism4

variable {L : ℕ} {hL : 4 ≤ L} {D : SigmaAdmissibleDynamics4 L hL}

/-- A transition automorphism maps valid Sigma paths to valid Sigma paths. -/
theorem map_path_valid
    (A : SigmaTransitionAutomorphism4 L D)
    {startVertex finishVertex : SigmaCoord4 L}
    {edges : List (SigmaFineEdge4 L)}
    (hpath :
      (sigmaTransitionSkeleton L).IsEdgePathFrom
        startVertex edges finishVertex) :
    (sigmaTransitionSkeleton L).IsEdgePathFrom
      (A.vertexEquiv startVertex) (edges.map A.edgeEquiv)
      (A.vertexEquiv finishVertex) := by
  induction edges generalizing startVertex with
  | nil =>
      change A.vertexEquiv finishVertex = A.vertexEquiv startVertex
      exact congrArg A.vertexEquiv hpath
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      constructor
      · change sigmaFineEdgeSource (A.edgeEquiv e) =
          A.vertexEquiv startVertex
        rw [A.source_map]
        change sigmaFineEdgeSource e = startVertex at hsource
        exact congrArg A.vertexEquiv hsource
      · change (sigmaTransitionSkeleton L).IsEdgePathFrom
          (sigmaFineEdgeTarget (A.edgeEquiv e))
          (List.map A.edgeEquiv rest) (A.vertexEquiv finishVertex)
        rw [A.target_map]
        change (sigmaTransitionSkeleton L).IsEdgePathFrom
          (sigmaFineEdgeTarget e) rest finishVertex at htail
        exact ih htail

/-- Apply a transition automorphism to every edge and endpoint of a history. -/
def mapHistory
    (A : SigmaTransitionAutomorphism4 L D)
    (H : SigmaTransitionHistory4 L) :
    SigmaTransitionHistory4 L where
  startVertex := A.vertexEquiv H.startVertex
  finishVertex := A.vertexEquiv H.finishVertex
  edges := H.edges.map A.edgeEquiv
  nonempty := by simpa using H.nonempty
  pathValid := A.map_path_valid H.pathValid

/-- Positive tension is preserved when a history is mapped. -/
theorem mapHistory_positive
    (A : SigmaTransitionAutomorphism4 L D)
    (H : SigmaTransitionHistory4 L)
    (hpositive : ∀ e, e ∈ H.edges → 0 < D.tension e) :
    ∀ e, e ∈ (A.mapHistory H).edges → 0 < D.tension e := by
  intro e he
  simp only [mapHistory, List.mem_map] at he
  obtain ⟨f, hf, rfl⟩ := he
  rw [A.tension_map]
  exact hpositive f hf

/-- Iterate a transition automorphism on a complete history. -/
def iterateHistory
    (A : SigmaTransitionAutomorphism4 L D) :
    ℕ → SigmaTransitionHistory4 L → SigmaTransitionHistory4 L
  | 0, H => H
  | n + 1, H => A.mapHistory (A.iterateHistory n H)

/-- Every iterate of a positive history remains positive. -/
theorem iterateHistory_positive
    (A : SigmaTransitionAutomorphism4 L D)
    (H : SigmaTransitionHistory4 L)
    (hpositive : ∀ e, e ∈ H.edges → 0 < D.tension e) :
    ∀ n e, e ∈ (A.iterateHistory n H).edges → 0 < D.tension e := by
  intro n
  induction n with
  | zero =>
      exact hpositive
  | succ n ih =>
      exact A.mapHistory_positive (A.iterateHistory n H) ih

/-- A fixed initial endpoint remains fixed under all history iterates. -/
theorem iterateHistory_start_of_fixed
    (A : SigmaTransitionAutomorphism4 L D)
    (H : SigmaTransitionHistory4 L)
    (hfix : A.vertexEquiv H.startVertex = H.startVertex) :
    ∀ n, (A.iterateHistory n H).startVertex = H.startVertex := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [iterateHistory, mapHistory, ih, hfix]

/-- A fixed terminal endpoint remains fixed under all history iterates. -/
theorem iterateHistory_finish_of_fixed
    (A : SigmaTransitionAutomorphism4 L D)
    (H : SigmaTransitionHistory4 L)
    (hfix : A.vertexEquiv H.finishVertex = H.finishVertex) :
    ∀ n, (A.iterateHistory n H).finishVertex = H.finishVertex := by
  intro n
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      simp [iterateHistory, mapHistory, ih, hfix]

end SigmaTransitionAutomorphism4

/-- A theorem-level source marking on actual Sigma transition edges.  The
marking is kept separate from a realization so that it cannot be chosen
independently for each path after the fact. -/
structure SigmaTransitionSource4 (d L : ℕ) where
  component : Fin (d + 1) → SigmaFineEdge4 L → ℝ

/-- A cyclic transition lift combines a dynamics-preserving history
automorphism with the corresponding cyclic action on source atoms.  The
component identity is the edge-level same-section equivariance needed to
transport source periods along the orbit. -/
structure CyclicSigmaTransitionLift
    (d L : ℕ) {hL : 4 ≤ L}
    (D : SigmaAdmissibleDynamics4 L hL)
    (Q : SigmaTransitionSource4 d L)
    extends SigmaTransitionAutomorphism4 L D where
  atomEquiv : Equiv.Perm (Fin (d + 1))
  sourceComponent_map :
    ∀ j e,
      Q.component (atomEquiv j) (edgeEquiv e) =
        Q.component j e

namespace CyclicSigmaTransitionLift

variable {d L : ℕ} {hL : 4 ≤ L}
  {D : SigmaAdmissibleDynamics4 L hL}
  {Q : SigmaTransitionSource4 d L}

/-- The `n`-fold cyclic permutation of source atoms. -/
def atomPow
    (C : CyclicSigmaTransitionLift d L D Q) (n : ℕ) :
    Equiv.Perm (Fin (d + 1)) :=
  C.atomEquiv ^ n

/-- Edge-level source equivariance integrates over any finite edge list. -/
theorem mapEdges_sourcePeriod
    (C : CyclicSigmaTransitionLift d L D Q)
    (edges : List (SigmaFineEdge4 L)) (j : Fin (d + 1)) :
    pathIntegral (Q.component (C.atomEquiv j))
        (edges.map C.edgeEquiv) =
      pathIntegral (Q.component j) edges := by
  induction edges with
  | nil =>
      simp [pathIntegral]
  | cons e rest ih =>
      simp [pathIntegral, C.sourceComponent_map, ih]

/-- Source periods are equivariant under one complete history map. -/
theorem mapHistory_sourcePeriod
    (C : CyclicSigmaTransitionLift d L D Q)
    (H : SigmaTransitionHistory4 L) (j : Fin (d + 1)) :
    pathIntegral (Q.component (C.atomEquiv j))
        (C.toSigmaTransitionAutomorphism4.mapHistory H).edges =
      pathIntegral (Q.component j) H.edges := by
  exact C.mapEdges_sourcePeriod H.edges j

/-- Source periods are equivariant under every cyclic history iterate. -/
theorem iterateHistory_sourcePeriod
    (C : CyclicSigmaTransitionLift d L D Q)
    (H : SigmaTransitionHistory4 L) (n : ℕ) (j : Fin (d + 1)) :
    pathIntegral (Q.component (C.atomPow n j))
        (C.toSigmaTransitionAutomorphism4.iterateHistory n H).edges =
      pathIntegral (Q.component j) H.edges := by
  induction n with
  | zero =>
      simp [atomPow, SigmaTransitionAutomorphism4.iterateHistory]
  | succ n ih =>
      have hatom :
          C.atomPow (n + 1) j =
            C.atomEquiv (C.atomPow n j) := by
        simp [atomPow, pow_succ', Equiv.Perm.mul_apply]
      rw [hatom]
      change pathIntegral
          (Q.component (C.atomEquiv (C.atomPow n j)))
          (C.toSigmaTransitionAutomorphism4.mapHistory
            (C.toSigmaTransitionAutomorphism4.iterateHistory n H)).edges =
        pathIntegral (Q.component j) H.edges
      rw [C.mapHistory_sourcePeriod]
      exact ih

/-- Equivalent component form of iterated source-period equivariance. -/
theorem iterateHistory_sourcePeriod_at
    (C : CyclicSigmaTransitionLift d L D Q)
    (H : SigmaTransitionHistory4 L) (n : ℕ) (j : Fin (d + 1)) :
    pathIntegral (Q.component j)
        (C.toSigmaTransitionAutomorphism4.iterateHistory n H).edges =
      pathIntegral (Q.component ((C.atomPow n).symm j)) H.edges := by
  have h :=
    C.iterateHistory_sourcePeriod H n ((C.atomPow n).symm j)
  simpa using h

end CyclicSigmaTransitionLift

/-- The additional criterion needed to register a finite cellular confluence
certificate as histories in the existing four-coordinate admissible Sigma
dynamics.  Each source channel is assigned an injectively indexed, nonempty,
forward-time Sigma history with common endpoints.  `sourcePeriodCompatibility`
requires the separately supplied transition-source marking to reproduce the
cellular source periods.  The canonical parallel-channel model alone does not
construct an instance of this structure. -/
structure SigmaSourceConfluenceRealization (d L : ℕ) (hL : 4 ≤ L)
    (V E F : Type*) [Fintype E] [Fintype F]
    (Q : SigmaTransitionSource4 d L)
    extends SourceBalancedConfluenceCertificate d V E F where
  dynamics : SigmaAdmissibleDynamics4 L hL
  sigmaStart : SigmaCoord4 L
  sigmaFinish : SigmaCoord4 L
  history : Fin (d + 1) → SigmaTransitionHistory4 L
  historyStart :
    ∀ i, (history i).startVertex = sigmaStart
  historyFinish :
    ∀ i, (history i).finishVertex = sigmaFinish
  historyInjective :
    Function.Injective history
  positiveTransition :
    ∀ i e, e ∈ (history i).edges → 0 < dynamics.tension e
  sourcePeriodCompatibility :
    ∀ i j,
      pathIntegral (Q.component j) (history i).edges =
        pathIntegral (sourceCochain j) (path i)

namespace SigmaSourceConfluenceRealization

variable {d L : ℕ} {hL : 4 ≤ L}
  {V E F : Type*} [Fintype E] [Fintype F]
  {Q : SigmaTransitionSource4 d L}

/-- A Sigma realization inherits the finite augmentation rank certificate. -/
theorem hasAugmentationRankCertificate
    (R : SigmaSourceConfluenceRealization d L hL V E F Q) :
    HasAugmentationRankCertificate d
      (fun i j =>
        pathIntegral (Q.component j) (R.history i).edges -
          R.commonOffset j) := by
  simpa [R.sourcePeriodCompatibility] using
    R.toSourceBalancedConfluenceCertificate.hasAugmentationRankCertificate

/-- The transition-source period of every registered Sigma history has the
required centered confluence value. -/
theorem historySourcePeriod
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    (i j : Fin (d + 1)) :
    pathIntegral (Q.component j) (R.history i).edges =
      R.commonOffset j + centeredAtom d i j := by
  rw [R.sourcePeriodCompatibility, R.pathValue]

/-- Every edge in a registered Sigma history has strictly increasing event
time. -/
theorem edgeEventTime_strict
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    {i : Fin (d + 1)} {e : SigmaFineEdge4 L}
    (he : e ∈ (R.history i).edges) :
    R.dynamics.eventTime (sigmaFineEdgeSource e) <
      R.dynamics.eventTime (sigmaFineEdgeTarget e) := by
  have ht := R.positiveTransition i e he
  rw [R.dynamics.tension_eq_time_div_scale e] at ht
  exact sub_pos.mp
    ((div_pos_iff_of_pos_right (R.dynamics.localScale_pos e)).mp ht)

/-- Every registered history advances strictly from the common Sigma start to
the common Sigma finish in event time. -/
theorem historyEventTime_strict
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    (i : Fin (d + 1)) :
    R.dynamics.eventTime R.sigmaStart <
      R.dynamics.eventTime R.sigmaFinish := by
  have h :=
    positiveSigmaPath_eventTime_strict R.dynamics
      (R.history i).pathValid (R.history i).nonempty
      (R.positiveTransition i)
  simpa [R.historyStart i, R.historyFinish i] using h

/-- The signed comparison loop of two realized Sigma histories, formed only at
the chain-comparison level and not as a reversed admissible transition. -/
def historyComparisonLoop
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    (i k : Fin (d + 1)) : List (SignedEdgeStep (SigmaFineEdge4 L)) :=
  signedForwardPath (R.history i).edges ++
    signedReversePath (R.history k).edges

/-- The source integral on a realized-history comparison loop is the exact
difference of the corresponding centered source atoms. -/
theorem historyComparisonLoop_sourcePeriod
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    (i k j : Fin (d + 1)) :
    signedPathIntegral (Q.component j) (R.historyComparisonLoop i k) =
      centeredAtom d i j - centeredAtom d k j := by
  simp only [historyComparisonLoop, signedPathIntegral_append,
    signedPathIntegral_forwardPath, signedPathIntegral_reversePath,
    sub_eq_add_neg]
  rw [R.historySourcePeriod, R.historySourcePeriod]
  ring

/-- If a same-edge candidate face universe fills a realized-history comparison
loop, the filling carries one unit of source curvature in the component of the
first history. -/
theorem historyComparisonLoop_filling_has_unitSourceFlux
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    {F' : Type*} [Fintype F']
    (K : FiniteTransportComplex (SigmaCoord4 L) (SigmaFineEdge4 L) F')
    {i k : Fin (d + 1)} (hik : i ≠ k)
    (S : F' → ℤ)
    (hfill :
      ∀ sigma : SigmaFineEdge4 L → ℝ,
        signedPathIntegral sigma (R.historyComparisonLoop i k) =
          edgePairing sigma (K.boundary2 S)) :
    facePairing (K.faceCoboundary (Q.component i)) S = 1 := by
  calc
    facePairing (K.faceCoboundary (Q.component i)) S =
        edgePairing (Q.component i) (K.boundary2 S) :=
          (finiteDiscreteStokesPairing K (Q.component i) S).symm
    _ = signedPathIntegral (Q.component i)
        (R.historyComparisonLoop i k) := (hfill (Q.component i)).symm
    _ = centeredAtom d i i - centeredAtom d k i :=
      R.historyComparisonLoop_sourcePeriod i k i
    _ = 1 := by
      simp [centeredAtom, Ne.symm hik]

/-- Closed source marking excludes every 2-chain filling of the comparison
loop of two distinct realized histories. -/
theorem historyComparisonLoop_not_boundsBy2Chain_of_closed
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    {F' : Type*} [Fintype F']
    (K : FiniteTransportComplex (SigmaCoord4 L) (SigmaFineEdge4 L) F')
    (hclosed : ∀ j, K.IsClosed1Cochain (Q.component j))
    {i k : Fin (d + 1)} (hik : i ≠ k) :
    ¬ SignedPathBoundsBy2Chain K (R.historyComparisonLoop i k) := by
  intro hbounds
  rcases hbounds with ⟨S, hfill⟩
  have hflux :=
    R.historyComparisonLoop_filling_has_unitSourceFlux K hik S hfill
  have hzero : facePairing (K.faceCoboundary (Q.component i)) S = 0 := by
    rw [hclosed i]
    simp [facePairing]
  linarith

end SigmaSourceConfluenceRealization

/-- The maximal source-admissible face hull of any same-edge candidate face
universe leaves every distinct realized-history comparison loop unfilled. -/
theorem historyComparisonLoop_not_bounds_in_sourceAdmissibleFaceHull
    {d L : ℕ} {hL : 4 ≤ L}
    {V E F : Type*} [Fintype E] [Fintype F]
    {Q : SigmaTransitionSource4 d L}
    (R : SigmaSourceConfluenceRealization d L hL V E F Q)
    {F' : Type*} [Fintype F']
    (K : FiniteTransportComplex (SigmaCoord4 L) (SigmaFineEdge4 L) F')
    {i k : Fin (d + 1)} (hik : i ≠ k) :
    ¬ SignedPathBoundsBy2Chain
      (sourceAdmissibleFaceHull K Q.component)
      (R.historyComparisonLoop i k) := by
  exact R.historyComparisonLoop_not_boundsBy2Chain_of_closed
    (sourceAdmissibleFaceHull K Q.component)
    (sourceAdmissibleFaceHull_closed K Q.component) hik

/-- A cyclic source-history orbit is the finite constructive input that reduces
`d + 1` independently supplied histories to one positive base history and one
source-equivariant transition automorphism.  The atom orbit is required to
enumerate the complete regular cyclic source family, while the base period and
offset conditions identify that orbit with the centered augmentation data. -/
structure CyclicSigmaHistoryOrbit
    (d L : ℕ) (hL : 4 ≤ L)
    (V E F : Type*) [Fintype E] [Fintype F]
    (Q : SigmaTransitionSource4 d L) where
  certificate : SourceBalancedConfluenceCertificate d V E F
  dynamics : SigmaAdmissibleDynamics4 L hL
  lift : CyclicSigmaTransitionLift d L dynamics Q
  baseHistory : SigmaTransitionHistory4 L
  basePositive :
    ∀ e, e ∈ baseHistory.edges → 0 < dynamics.tension e
  baseAtom : Fin (d + 1)
  atomOrbit :
    ∀ i, lift.atomPow i.val baseAtom = i
  startFixed :
    lift.vertexEquiv baseHistory.startVertex = baseHistory.startVertex
  finishFixed :
    lift.vertexEquiv baseHistory.finishVertex = baseHistory.finishVertex
  offsetInvariant :
    ∀ n j,
      certificate.commonOffset ((lift.atomPow n).symm j) =
        certificate.commonOffset j
  baseSourcePeriod :
    ∀ j,
      pathIntegral (Q.component j) baseHistory.edges =
        certificate.commonOffset j + centeredAtom d baseAtom j

namespace CyclicSigmaHistoryOrbit

variable {d L : ℕ} {hL : 4 ≤ L}
  {V E F : Type*} [Fintype E] [Fintype F]
  {Q : SigmaTransitionSource4 d L}

/-- The source-indexed history family generated from the base history. -/
def history
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q)
    (i : Fin (d + 1)) :
    SigmaTransitionHistory4 L :=
  O.lift.toSigmaTransitionAutomorphism4.iterateHistory i.val O.baseHistory

/-- Every generated history has the base initial endpoint. -/
theorem history_start
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q)
    (i : Fin (d + 1)) :
    (O.history i).startVertex = O.baseHistory.startVertex :=
  O.lift.toSigmaTransitionAutomorphism4.iterateHistory_start_of_fixed
    O.baseHistory O.startFixed i.val

/-- Every generated history has the base terminal endpoint. -/
theorem history_finish
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q)
    (i : Fin (d + 1)) :
    (O.history i).finishVertex = O.baseHistory.finishVertex :=
  O.lift.toSigmaTransitionAutomorphism4.iterateHistory_finish_of_fixed
    O.baseHistory O.finishFixed i.val

/-- Every generated history remains positive in the admissible dynamics. -/
theorem history_positive
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q)
    (i : Fin (d + 1)) :
    ∀ e, e ∈ (O.history i).edges → 0 < O.dynamics.tension e :=
  O.lift.toSigmaTransitionAutomorphism4.iterateHistory_positive
    O.baseHistory O.basePositive i.val

/-- Cyclic equivariance transports the base period to the exact centered
source period of every generated history. -/
theorem history_sourcePeriod
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q)
    (i j : Fin (d + 1)) :
    pathIntegral (Q.component j) (O.history i).edges =
      O.certificate.commonOffset j + centeredAtom d i j := by
  let p := O.lift.atomPow i.val
  calc
    pathIntegral (Q.component j) (O.history i).edges =
        pathIntegral (Q.component (p.symm j)) O.baseHistory.edges := by
          exact O.lift.iterateHistory_sourcePeriod_at
            O.baseHistory i.val j
    _ = O.certificate.commonOffset (p.symm j) +
        centeredAtom d O.baseAtom (p.symm j) :=
          O.baseSourcePeriod (p.symm j)
    _ = O.certificate.commonOffset j +
        centeredAtom d (p O.baseAtom) j := by
          rw [O.offsetInvariant]
          have hc :=
            centeredAtom_equivariant p O.baseAtom (p.symm j)
          simpa using hc.symm
    _ = O.certificate.commonOffset j + centeredAtom d i j := by
          rw [O.atomOrbit]

/-- Distinct atoms generate distinct histories because their centered source
period vectors are distinct. -/
theorem history_injective
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q) :
    Function.Injective O.history := by
  intro i k heq
  apply centeredAtom_injective d
  funext j
  have hi := O.history_sourcePeriod i j
  have hk := O.history_sourcePeriod k j
  rw [heq] at hi
  linarith

/-- Main constructive bridge: one regular cyclic source-history orbit supplies
the complete Sigma source-confluence realization required by the TeX
source-balanced confluence theorem. -/
noncomputable def toSigmaSourceConfluenceRealization
    (O : CyclicSigmaHistoryOrbit d L hL V E F Q) :
    SigmaSourceConfluenceRealization d L hL V E F Q where
  toSourceBalancedConfluenceCertificate := O.certificate
  dynamics := O.dynamics
  sigmaStart := O.baseHistory.startVertex
  sigmaFinish := O.baseHistory.finishVertex
  history := O.history
  historyStart := O.history_start
  historyFinish := O.history_finish
  historyInjective := O.history_injective
  positiveTransition := O.history_positive
  sourcePeriodCompatibility := by
    intro i j
    rw [O.history_sourcePeriod, O.certificate.pathValue]

end CyclicSigmaHistoryOrbit

namespace ConcreteFourCoordinateModel

/-!
## Canonical rank-three transition model

The constructions below realize the conditional cyclic-history theorem on the
concrete four-coordinate Sigma transition grid.  The four coordinate axes are
the four source atoms of the rank-three augmentation carrier.  Cyclic
coordinate rotation preserves the concrete Sigma tension, and four cyclic
orders of the same four forward coordinate steps give positive histories with
common endpoints.

This is the finite source-generated transition model corresponding to the
transition-realization boundary in `discrete_noether_sigma_v3.tex`.  It proves
that the boundary is inhabited by actual Sigma fine-edge histories.  It does
not identify an independently prescribed physical transition network with
this canonical coordinate model.
-/

/-- The regular four-cycle on the coordinate axes and source atoms. -/
def axisCycle : Equiv.Perm (Fin 4) where
  toFun := ![(1 : Fin 4), 2, 3, 0]
  invFun := ![(3 : Fin 4), 0, 1, 2]
  left_inv := by
    intro i
    fin_cases i <;> rfl
  right_inv := by
    intro i
    fin_cases i <;> rfl

/-- Rotate four-coordinate Sigma states together with `axisCycle`. -/
def coordCycle {L : ℕ} (x : SigmaCoord4 L) : SigmaCoord4 L :=
  (((x.2, x.1.1.1), x.1.1.2), x.1.2)

/-- The inverse four-coordinate rotation. -/
def coordCycleInv {L : ℕ} (x : SigmaCoord4 L) : SigmaCoord4 L :=
  (((x.1.1.2, x.1.2), x.2), x.1.1.1)

/-- Coordinate rotation as a permutation of the Sigma state space. -/
def coordCycleEquiv (L : ℕ) : Equiv.Perm (SigmaCoord4 L) where
  toFun := coordCycle
  invFun := coordCycleInv
  left_inv := by
    rintro ⟨⟨⟨x₀, x₁⟩, x₂⟩, x₃⟩
    rfl
  right_inv := by
    rintro ⟨⟨⟨x₀, x₁⟩, x₂⟩, x₃⟩
    rfl

@[simp]
theorem coordCycle_get {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4) :
    sigmaCoord4Get (coordCycle x) (axisCycle axis) =
      sigmaCoord4Get x axis := by
  fin_cases axis <;>
    simp [axisCycle, coordCycle, sigmaCoord4Get]

@[simp]
theorem coordCycleInv_get {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4) :
    sigmaCoord4Get (coordCycleInv x) (axisCycle.symm axis) =
      sigmaCoord4Get x axis := by
  fin_cases axis <;>
    simp [axisCycle, coordCycleInv, sigmaCoord4Get]

@[simp]
theorem coordCycle_set {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (v : Fin L) :
    coordCycle (sigmaCoord4Set x axis v) =
      sigmaCoord4Set (coordCycle x) (axisCycle axis) v := by
  fin_cases axis <;>
    simp [axisCycle, coordCycle, sigmaCoord4Set]

@[simp]
theorem coordCycleInv_set {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (v : Fin L) :
    coordCycleInv (sigmaCoord4Set x axis v) =
      sigmaCoord4Set (coordCycleInv x) (axisCycle.symm axis) v := by
  fin_cases axis <;>
    simp [axisCycle, coordCycleInv, sigmaCoord4Set]

/-- Rotate a Sigma fine edge together with its source and coordinate axis. -/
def edgeCycle {L : ℕ} (e : SigmaFineEdge4 L) : SigmaFineEdge4 L := by
  refine ⟨((coordCycle (sigmaFineEdgeSource e),
    axisCycle (sigmaFineEdgeAxis e)), sigmaFineEdgeForward e), ?_⟩
  simpa [SigmaFineEdgeValid4, sigmaFineEdgeSource, sigmaFineEdgeAxis,
    sigmaFineEdgeForward] using e.2

/-- Inverse rotation of a Sigma fine edge. -/
def edgeCycleInv {L : ℕ} (e : SigmaFineEdge4 L) : SigmaFineEdge4 L := by
  refine ⟨((coordCycleInv (sigmaFineEdgeSource e),
    axisCycle.symm (sigmaFineEdgeAxis e)), sigmaFineEdgeForward e), ?_⟩
  simpa [SigmaFineEdgeValid4, sigmaFineEdgeSource, sigmaFineEdgeAxis,
    sigmaFineEdgeForward] using e.2

@[simp]
theorem edgeCycle_source {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeSource (edgeCycle e) =
      coordCycle (sigmaFineEdgeSource e) :=
  rfl

@[simp]
theorem edgeCycle_axis {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeAxis (edgeCycle e) =
      axisCycle (sigmaFineEdgeAxis e) :=
  rfl

@[simp]
theorem edgeCycle_forward {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeForward (edgeCycle e) = sigmaFineEdgeForward e :=
  rfl

@[simp]
theorem edgeCycleInv_source {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeSource (edgeCycleInv e) =
      coordCycleInv (sigmaFineEdgeSource e) :=
  rfl

@[simp]
theorem edgeCycleInv_axis {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeAxis (edgeCycleInv e) =
      axisCycle.symm (sigmaFineEdgeAxis e) :=
  rfl

@[simp]
theorem edgeCycleInv_forward {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeForward (edgeCycleInv e) = sigmaFineEdgeForward e :=
  rfl

@[simp]
theorem edgeCycle_stepTarget {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeStepTarget (edgeCycle e) =
      sigmaFineEdgeStepTarget e := by
  apply Fin.ext
  by_cases hf : sigmaFineEdgeForward e = true
  · have hfCycle : sigmaFineEdgeForward (edgeCycle e) = true := by
      simpa using hf
    rw [sigmaFineEdgeStepTarget_val_forward _ hfCycle,
      sigmaFineEdgeStepTarget_val_forward e hf]
    simp
  · have hfalse : sigmaFineEdgeForward e = false :=
      Bool.eq_false_of_not_eq_true hf
    have hfalseCycle : sigmaFineEdgeForward (edgeCycle e) = false := by
      simpa using hfalse
    rw [sigmaFineEdgeStepTarget_val_backward _ hfalseCycle,
      sigmaFineEdgeStepTarget_val_backward e hfalse]
    simp

@[simp]
theorem edgeCycleInv_stepTarget {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeStepTarget (edgeCycleInv e) =
      sigmaFineEdgeStepTarget e := by
  apply Fin.ext
  by_cases hf : sigmaFineEdgeForward e = true
  · have hfCycle : sigmaFineEdgeForward (edgeCycleInv e) = true := by
      simpa using hf
    rw [sigmaFineEdgeStepTarget_val_forward _ hfCycle,
      sigmaFineEdgeStepTarget_val_forward e hf]
    simp
  · have hfalse : sigmaFineEdgeForward e = false :=
      Bool.eq_false_of_not_eq_true hf
    have hfalseCycle : sigmaFineEdgeForward (edgeCycleInv e) = false := by
      simpa using hfalse
    rw [sigmaFineEdgeStepTarget_val_backward _ hfalseCycle,
      sigmaFineEdgeStepTarget_val_backward e hfalse]
    simp

@[simp]
theorem edgeCycle_target {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeTarget (edgeCycle e) =
      coordCycle (sigmaFineEdgeTarget e) := by
  simp [sigmaFineEdgeTarget]

@[simp]
theorem edgeCycleInv_target {L : ℕ} (e : SigmaFineEdge4 L) :
    sigmaFineEdgeTarget (edgeCycleInv e) =
      coordCycleInv (sigmaFineEdgeTarget e) := by
  simp [sigmaFineEdgeTarget]

/-- Edge rotation as a permutation of the concrete Sigma transition set. -/
def edgeCycleEquiv (L : ℕ) : Equiv.Perm (SigmaFineEdge4 L) where
  toFun := edgeCycle
  invFun := edgeCycleInv
  left_inv := by
    intro e
    apply Subtype.ext
    rcases e with ⟨⟨⟨x, axis⟩, forward⟩, valid⟩
    fin_cases axis <;>
      simp [edgeCycle, edgeCycleInv, coordCycle, coordCycleInv, axisCycle,
        sigmaFineEdgeSource, sigmaFineEdgeAxis, sigmaFineEdgeForward]
  right_inv := by
    intro e
    apply Subtype.ext
    rcases e with ⟨⟨⟨x, axis⟩, forward⟩, valid⟩
    fin_cases axis <;>
      simp [edgeCycle, edgeCycleInv, coordCycle, coordCycleInv, axisCycle,
        sigmaFineEdgeSource, sigmaFineEdgeAxis, sigmaFineEdgeForward]

/-- The zero coordinate used as the common source event. -/
def levelZero (L : ℕ) (hL : 4 ≤ L) : Fin L :=
  ⟨0, by omega⟩

/-- The first positive coordinate used as the common target event. -/
def levelOne (L : ℕ) (hL : 4 ≤ L) : Fin L :=
  ⟨1, by omega⟩

/-- Coordinate state after the first `k` steps of the base history. -/
def baseState0 (L : ℕ) (hL : 4 ≤ L) : SigmaCoord4 L :=
  (((levelZero L hL, levelZero L hL), levelZero L hL), levelZero L hL)

def baseState1 (L : ℕ) (hL : 4 ≤ L) : SigmaCoord4 L :=
  (((levelOne L hL, levelZero L hL), levelZero L hL), levelZero L hL)

def baseState2 (L : ℕ) (hL : 4 ≤ L) : SigmaCoord4 L :=
  (((levelOne L hL, levelOne L hL), levelZero L hL), levelZero L hL)

def baseState3 (L : ℕ) (hL : 4 ≤ L) : SigmaCoord4 L :=
  (((levelOne L hL, levelOne L hL), levelOne L hL), levelZero L hL)

def baseState4 (L : ℕ) (hL : 4 ≤ L) : SigmaCoord4 L :=
  (((levelOne L hL, levelOne L hL), levelOne L hL), levelOne L hL)

/-- A forward fine edge at a state and coordinate axis. -/
def forwardEdge {L : ℕ} (x : SigmaCoord4 L) (axis : Fin 4)
    (hvalid : (sigmaCoord4Get x axis).val + 1 < L) :
    SigmaFineEdge4 L :=
  ⟨((x, axis), true), by
    simpa [SigmaFineEdgeValid4] using hvalid⟩

@[simp]
theorem forwardEdge_source {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (hvalid : (sigmaCoord4Get x axis).val + 1 < L) :
    sigmaFineEdgeSource (forwardEdge x axis hvalid) = x :=
  rfl

@[simp]
theorem forwardEdge_axis {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (hvalid : (sigmaCoord4Get x axis).val + 1 < L) :
    sigmaFineEdgeAxis (forwardEdge x axis hvalid) = axis :=
  rfl

@[simp]
theorem forwardEdge_forward {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (hvalid : (sigmaCoord4Get x axis).val + 1 < L) :
    sigmaFineEdgeForward (forwardEdge x axis hvalid) = true :=
  rfl

@[simp]
theorem forwardEdge_stepTarget {L : ℕ} (x : SigmaCoord4 L)
    (axis : Fin 4) (hvalid : (sigmaCoord4Get x axis).val + 1 < L) :
    sigmaFineEdgeStepTarget (forwardEdge x axis hvalid) =
      ⟨(sigmaCoord4Get x axis).val + 1, hvalid⟩ := by
  apply Fin.ext
  rw [sigmaFineEdgeStepTarget_val_forward _ (forwardEdge_forward _ _ _)]
  simp

def baseEdge0 (L : ℕ) (hL : 4 ≤ L) : SigmaFineEdge4 L :=
  forwardEdge (baseState0 L hL) 0 (by
    simp [baseState0, levelZero, sigmaCoord4Get]
    omega)

def baseEdge1 (L : ℕ) (hL : 4 ≤ L) : SigmaFineEdge4 L :=
  forwardEdge (baseState1 L hL) 1 (by
    simp [baseState1, levelZero, sigmaCoord4Get]
    omega)

def baseEdge2 (L : ℕ) (hL : 4 ≤ L) : SigmaFineEdge4 L :=
  forwardEdge (baseState2 L hL) 2 (by
    simp [baseState2, levelZero, sigmaCoord4Get]
    omega)

def baseEdge3 (L : ℕ) (hL : 4 ≤ L) : SigmaFineEdge4 L :=
  forwardEdge (baseState3 L hL) 3 (by
    simp [baseState3, levelZero, sigmaCoord4Get]
    omega)

@[simp]
theorem baseEdge0_source (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeSource (baseEdge0 L hL) = baseState0 L hL :=
  rfl

@[simp]
theorem baseEdge1_source (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeSource (baseEdge1 L hL) = baseState1 L hL :=
  rfl

@[simp]
theorem baseEdge2_source (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeSource (baseEdge2 L hL) = baseState2 L hL :=
  rfl

@[simp]
theorem baseEdge3_source (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeSource (baseEdge3 L hL) = baseState3 L hL :=
  rfl

@[simp]
theorem baseEdge0_target (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeTarget (baseEdge0 L hL) = baseState1 L hL := by
  simp [baseEdge0, sigmaFineEdgeTarget,
    baseState0, baseState1, levelZero, levelOne,
    sigmaCoord4Get, sigmaCoord4Set]

@[simp]
theorem baseEdge1_target (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeTarget (baseEdge1 L hL) = baseState2 L hL := by
  simp [baseEdge1, sigmaFineEdgeTarget,
    baseState1, baseState2, levelZero, levelOne,
    sigmaCoord4Get, sigmaCoord4Set]

@[simp]
theorem baseEdge2_target (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeTarget (baseEdge2 L hL) = baseState3 L hL := by
  simp [baseEdge2, sigmaFineEdgeTarget,
    baseState2, baseState3, levelZero, levelOne,
    sigmaCoord4Get, sigmaCoord4Set]

@[simp]
theorem baseEdge3_target (L : ℕ) (hL : 4 ≤ L) :
    sigmaFineEdgeTarget (baseEdge3 L hL) = baseState4 L hL := by
  simp [baseEdge3, sigmaFineEdgeTarget,
    baseState3, baseState4, levelZero, levelOne,
    sigmaCoord4Get, sigmaCoord4Set]

/-- The positive four-step base history from the zero to the unit state. -/
def baseHistory (L : ℕ) (hL : 4 ≤ L) : SigmaTransitionHistory4 L where
  startVertex := baseState0 L hL
  finishVertex := baseState4 L hL
  edges :=
    [baseEdge0 L hL, baseEdge1 L hL, baseEdge2 L hL, baseEdge3 L hL]
  nonempty := by simp
  pathValid := by
    constructor
    · exact baseEdge0_source L hL
    · change (sigmaTransitionSkeleton L).IsEdgePathFrom
        (sigmaFineEdgeTarget (baseEdge0 L hL))
        [baseEdge1 L hL, baseEdge2 L hL, baseEdge3 L hL]
        (baseState4 L hL)
      rw [baseEdge0_target]
      constructor
      · exact baseEdge1_source L hL
      · change (sigmaTransitionSkeleton L).IsEdgePathFrom
          (sigmaFineEdgeTarget (baseEdge1 L hL))
          [baseEdge2 L hL, baseEdge3 L hL] (baseState4 L hL)
        rw [baseEdge1_target]
        constructor
        · exact baseEdge2_source L hL
        · change (sigmaTransitionSkeleton L).IsEdgePathFrom
            (sigmaFineEdgeTarget (baseEdge2 L hL))
            [baseEdge3 L hL] (baseState4 L hL)
          rw [baseEdge2_target]
          constructor
          · exact baseEdge3_source L hL
          · change (baseState4 L hL) =
              sigmaFineEdgeTarget (baseEdge3 L hL)
            rw [baseEdge3_target]

@[simp]
theorem coordCycle_baseState0 (L : ℕ) (hL : 4 ≤ L) :
    coordCycle (baseState0 L hL) = baseState0 L hL :=
  rfl

@[simp]
theorem coordCycle_baseState4 (L : ℕ) (hL : 4 ≤ L) :
    coordCycle (baseState4 L hL) = baseState4 L hL :=
  rfl

theorem baseState1_ne_baseState0 (L : ℕ) (hL : 4 ≤ L) :
    baseState1 L hL ≠ baseState0 L hL := by
  intro h
  have hcoord := congrArg (fun x => sigmaCoord4Get x 0) h
  simp [baseState0, baseState1, levelZero, levelOne,
    sigmaCoord4Get] at hcoord

theorem baseState2_ne_baseState0 (L : ℕ) (hL : 4 ≤ L) :
    baseState2 L hL ≠ baseState0 L hL := by
  intro h
  have hcoord := congrArg (fun x => sigmaCoord4Get x 0) h
  simp [baseState0, baseState2, levelZero, levelOne,
    sigmaCoord4Get] at hcoord

theorem baseState3_ne_baseState0 (L : ℕ) (hL : 4 ≤ L) :
    baseState3 L hL ≠ baseState0 L hL := by
  intro h
  have hcoord := congrArg (fun x => sigmaCoord4Get x 0) h
  simp [baseState0, baseState3, levelZero, levelOne,
    sigmaCoord4Get] at hcoord

/-- The uncentered atomic incidence on the concrete Sigma transition
skeleton.  An edge leaving the common source event carries the basis atom
selected by its coordinate axis; every other edge carries zero.

This is the Lean realization of the raw transition-chain incidence used in
`discrete_noether_sigma_v3.tex`.  Its augmentation projection is proved below
to equal the centered source marking. -/
noncomputable def rawSourceMarking (L : ℕ) (hL : 4 ≤ L) :
    SigmaTransitionSource4 3 L where
  component := fun i e =>
    if sigmaFineEdgeSource e = baseState0 L hL then
      if sigmaFineEdgeAxis e = i then 1 else 0
    else
      0

/-- Coordinate and source rotation preserve the raw atomic incidence. -/
theorem rawSourceMarking_equivariant
    (L : ℕ) (hL : 4 ≤ L) (i : Fin 4) (e : SigmaFineEdge4 L) :
    (rawSourceMarking L hL).component (axisCycle i) (edgeCycle e) =
      (rawSourceMarking L hL).component i e := by
  by_cases hs : sigmaFineEdgeSource e = baseState0 L hL
  · simp [rawSourceMarking, hs]
  · have hsCycle :
        coordCycle (sigmaFineEdgeSource e) ≠ baseState0 L hL := by
      intro h
      apply hs
      have hrot :
          coordCycle (sigmaFineEdgeSource e) =
            coordCycle (baseState0 L hL) := by
        simpa using h
      exact (coordCycleEquiv L).injective hrot
    simp [rawSourceMarking, hs, hsCycle]

/-- The raw atomic period of the base history is the zeroth basis atom. -/
theorem rawSourceMarking_baseHistory_period
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    pathIntegral ((rawSourceMarking L hL).component j)
        (baseHistory L hL).edges =
      if (0 : Fin 4) = j then 1 else 0 := by
  fin_cases j <;>
    simp [rawSourceMarking, baseHistory, pathIntegral,
      baseEdge0, baseEdge1, baseEdge2, baseEdge3,
      baseState1_ne_baseState0, baseState2_ne_baseState0,
      baseState3_ne_baseState0]

/-- The canonical rank-three source marking.  Only an edge leaving the common
source event contributes, and its coordinate axis supplies the source atom. -/
noncomputable def sourceMarking (L : ℕ) (hL : 4 ≤ L) :
    SigmaTransitionSource4 3 L where
  component := fun j e =>
    if sigmaFineEdgeSource e = baseState0 L hL then
      centeredAtom 3 (sigmaFineEdgeAxis e) j
    else
      0

/-- The four source components of every marked edge sum to zero. -/
theorem sourceMarking_component_sum
    (L : ℕ) (hL : 4 ≤ L) (e : SigmaFineEdge4 L) :
    ∑ j, (sourceMarking L hL).component j e = 0 := by
  by_cases hs : sigmaFineEdgeSource e = baseState0 L hL
  · simp [sourceMarking, hs, centeredAtom_component_sum]
  · simp [sourceMarking, hs]

/-- Coordinate and source rotation preserve the canonical edge marking. -/
theorem sourceMarking_equivariant
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) (e : SigmaFineEdge4 L) :
    (sourceMarking L hL).component (axisCycle j) (edgeCycle e) =
      (sourceMarking L hL).component j e := by
  by_cases hs : sigmaFineEdgeSource e = baseState0 L hL
  · simp [sourceMarking, hs,
      centeredAtom_equivariant axisCycle (sigmaFineEdgeAxis e) j]
  · have hsCycle :
        coordCycle (sigmaFineEdgeSource e) ≠ baseState0 L hL := by
      intro h
      apply hs
      have hrot :
          coordCycle (sigmaFineEdgeSource e) =
            coordCycle (baseState0 L hL) := by
        simpa using h
      exact (coordCycleEquiv L).injective hrot
    simp [sourceMarking, hs, hsCycle]

/-- Cyclic coordinate rotation is an automorphism of the concrete Sigma
dynamics and preserves orientation tension. -/
noncomputable def transitionAutomorphism (L : ℕ) (hL : 4 ≤ L) :
    SigmaTransitionAutomorphism4 L (concreteSigmaAdmissibleDynamics4 L hL) where
  vertexEquiv := coordCycleEquiv L
  edgeEquiv := edgeCycleEquiv L
  source_map := by
    intro e
    exact edgeCycle_source e
  target_map := by
    intro e
    exact edgeCycle_target e
  tension_map := by
    intro e
    simp [concreteSigmaAdmissibleDynamics4, sigmaOrientationTension,
      edgeCycleEquiv]

/-- The concrete transition automorphism with the raw atomic marking is a
source-equivariant cyclic lift. -/
noncomputable def rawTransitionLift (L : ℕ) (hL : 4 ≤ L) :
    CyclicSigmaTransitionLift 3 L
      (concreteSigmaAdmissibleDynamics4 L hL) (rawSourceMarking L hL) where
  toSigmaTransitionAutomorphism4 := transitionAutomorphism L hL
  atomEquiv := axisCycle
  sourceComponent_map := rawSourceMarking_equivariant L hL

/-- The concrete coordinate rotation and edge marking form the required
source-equivariant cyclic transition lift. -/
noncomputable def transitionLift (L : ℕ) (hL : 4 ≤ L) :
    CyclicSigmaTransitionLift 3 L
      (concreteSigmaAdmissibleDynamics4 L hL) (sourceMarking L hL) where
  toSigmaTransitionAutomorphism4 := transitionAutomorphism L hL
  atomEquiv := axisCycle
  sourceComponent_map := sourceMarking_equivariant L hL

/-- Every edge of the base history has positive concrete Sigma tension. -/
theorem baseHistory_positive (L : ℕ) (hL : 4 ≤ L) :
    ∀ e, e ∈ (baseHistory L hL).edges →
      0 < (concreteSigmaAdmissibleDynamics4 L hL).tension e := by
  intro e he
  have he' :
      e = baseEdge0 L hL ∨ e = baseEdge1 L hL ∨
        e = baseEdge2 L hL ∨ e = baseEdge3 L hL := by
    simpa only [baseHistory, List.mem_cons, List.not_mem_nil, or_false] using he
  rcases he' with rfl | rfl | rfl | rfl <;>
    norm_num [concreteSigmaAdmissibleDynamics4, sigmaOrientationTension,
      baseEdge0, baseEdge1, baseEdge2, baseEdge3, forwardEdge,
      sigmaFineEdgeForward]

@[simp]
theorem sourceMarking_baseEdge0
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (sourceMarking L hL).component j (baseEdge0 L hL) =
      centeredAtom 3 0 j := by
  simp [sourceMarking, baseEdge0]

@[simp]
theorem sourceMarking_baseEdge1
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (sourceMarking L hL).component j (baseEdge1 L hL) = 0 := by
  simp [sourceMarking, baseEdge1, baseState1_ne_baseState0]

@[simp]
theorem sourceMarking_baseEdge2
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (sourceMarking L hL).component j (baseEdge2 L hL) = 0 := by
  simp [sourceMarking, baseEdge2, baseState2_ne_baseState0]

@[simp]
theorem sourceMarking_baseEdge3
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (sourceMarking L hL).component j (baseEdge3 L hL) = 0 := by
  simp [sourceMarking, baseEdge3, baseState3_ne_baseState0]

/-- The base path carries exactly the centered source period of atom zero. -/
theorem baseHistory_sourcePeriod
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    pathIntegral ((sourceMarking L hL).component j)
        (baseHistory L hL).edges =
      centeredAtom 3 0 j := by
  simp [baseHistory, pathIntegral]

/-- Four cyclic iterates of atom zero enumerate all source atoms. -/
theorem axisCycle_orbit_zero (i : Fin 4) :
    (axisCycle ^ i.val) 0 = i := by
  fin_cases i <;> decide

/-- The concrete four-coordinate data inhabit the cyclic Sigma-history
criterion in rank three. -/
noncomputable def cyclicHistoryOrbit (L : ℕ) (hL : 4 ≤ L) :
    CyclicSigmaHistoryOrbit 3 L hL
      ParallelVertex (ParallelEdge 3) ParallelFace (sourceMarking L hL) where
  certificate := parallelChannelCertificate 3
  dynamics := concreteSigmaAdmissibleDynamics4 L hL
  lift := transitionLift L hL
  baseHistory := baseHistory L hL
  basePositive := baseHistory_positive L hL
  baseAtom := 0
  atomOrbit := axisCycle_orbit_zero
  startFixed := coordCycle_baseState0 L hL
  finishFixed := coordCycle_baseState4 L hL
  offsetInvariant := by
    intro n j
    rfl
  baseSourcePeriod := by
    intro j
    change pathIntegral ((sourceMarking L hL).component j)
        (baseHistory L hL).edges =
      0 + centeredAtom 3 0 j
    simpa using baseHistory_sourcePeriod L hL j

/-- The cyclic histories carry the uncentered atomic period vectors before
augmentation projection. -/
theorem rawSourceMarking_history_period
    (L : ℕ) (hL : 4 ≤ L) (i j : Fin 4) :
    pathIntegral ((rawSourceMarking L hL).component j)
        ((cyclicHistoryOrbit L hL).history i).edges =
      if i = j then 1 else 0 := by
  let p : Equiv.Perm (Fin 4) := (rawTransitionLift L hL).atomPow i.val
  have hperiod :=
    (rawTransitionLift L hL).iterateHistory_sourcePeriod_at
      (baseHistory L hL) i.val j
  have hp : p 0 = i := by
    exact axisCycle_orbit_zero i
  change
    pathIntegral ((rawSourceMarking L hL).component j)
        ((rawTransitionLift L hL).toSigmaTransitionAutomorphism4.iterateHistory
          i.val (baseHistory L hL)).edges =
      if i = j then 1 else 0
  rw [hperiod, rawSourceMarking_baseHistory_period]
  have hiff : (0 : Fin 4) = p.symm j ↔ i = j := by
    constructor
    · intro h
      simpa [hp] using congrArg p h
    · intro h
      subst j
      exact (p.symm_apply_eq.mpr hp.symm).symm
  exact if_congr hiff rfl rfl

/-- The actual four-coordinate Sigma transition skeleton supplies the raw
atomic incidence certificate whose distinguished periods are the four basis
atoms.  No additional faces are inserted into the source-generated
one-skeleton. -/
noncomputable def rawAtomicSourceIncidenceCertificate
    (L : ℕ) (hL : 4 ≤ L) :
    RawAtomicSourceIncidenceCertificate 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty where
  complex := sigmaTransitionSkeleton L
  startVertex := baseState0 L hL
  finishVertex := baseState4 L hL
  path := fun i => ((cyclicHistoryOrbit L hL).history i).edges
  pathValid := by
    intro i
    have hpath := ((cyclicHistoryOrbit L hL).history i).pathValid
    simpa [(cyclicHistoryOrbit L hL).history_start i,
      (cyclicHistoryOrbit L hL).history_finish i] using hpath
  rawSource := (rawSourceMarking L hL).component
  rawFaceCommonMode := by
    intro f
    exact nomatch f
  rawOffset := 0
  rawPathValue := by
    intro i j
    simpa using rawSourceMarking_history_period L hL i j

/-- Augmentation projection of the raw concrete incidence is exactly the
centered source marking already used by the Sigma confluence realization. -/
theorem rawAtomicSourceIncidence_projected_eq_sourceMarking
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) (e : SigmaFineEdge4 L) :
    (rawAtomicSourceIncidenceCertificate L hL).projectedSourceCochain j e =
      (sourceMarking L hL).component j e := by
  classical
  by_cases hs : sigmaFineEdgeSource e = baseState0 L hL
  · simp [RawAtomicSourceIncidenceCertificate.projectedSourceCochain,
      rawAtomicSourceIncidenceCertificate, rawSourceMarking,
      sourceMarking, hs]
  · simp [RawAtomicSourceIncidenceCertificate.projectedSourceCochain,
      rawAtomicSourceIncidenceCertificate, rawSourceMarking,
      sourceMarking, hs]

/-- Main rank-three realization theorem: the concrete four-coordinate Sigma
grid supplies the complete source-balanced transition realization. -/
noncomputable def sigmaSourceConfluenceRealization
    (L : ℕ) (hL : 4 ≤ L) :
    SigmaSourceConfluenceRealization 3 L hL
      ParallelVertex (ParallelEdge 3) ParallelFace (sourceMarking L hL) :=
  (cyclicHistoryOrbit L hL).toSigmaSourceConfluenceRealization

end ConcreteFourCoordinateModel

end SourceConfluence
end Hardtest
