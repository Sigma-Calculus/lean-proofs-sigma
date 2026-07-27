/-
Copyright (c) 2026 Oliver Sievers. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Oliver Sievers
-/

import Hardtest.SourceConfluence

/-!
# Source-equivariant transition orbits

This file connects a single source-equivariant transition orbit to the raw
source-incidence and source-balanced confluence certificates formalized in
`Hardtest.SourceConfluence`.

## TeX correspondence

The paper-facing source is `discrete_noether_sigma_v3.tex`.  The relevant
statements are the definition of raw atomic source incidence, the augmentation
projection theorem, and the source-balanced confluence theorem.  This module
formalizes two intervening finite criteria.  First, one common-endpoint base
path, one incidence-preserving cyclic transition automorphism, and one
equivariant raw edge-source readout generate the complete distinguished path
family.  Second, a regular equivariant orbit of outgoing source edges
canonically induces that raw readout as an atomic indicator incidence.

The construction does not assert that an independently prescribed physical
transition network supplies the required source-edge orbit or the cyclic
automorphism.  Those remain same-section realization data.
-/

namespace Hardtest
namespace SourceConfluence

open scoped BigOperators
open GaugeTransport
open GaugeTransport.FiniteTransportComplex

/-- An incidence-preserving automorphism of a finite transition complex. -/
structure TransitionComplexAutomorphism
    (V E F : Type*) [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F) where
  vertexEquiv : Equiv.Perm V
  edgeEquiv : Equiv.Perm E
  source_map :
    ∀ e, K.source (edgeEquiv e) = vertexEquiv (K.source e)
  target_map :
    ∀ e, K.target (edgeEquiv e) = vertexEquiv (K.target e)

namespace TransitionComplexAutomorphism

variable {V E F : Type*} [Fintype E] [Fintype F]
  {K : FiniteTransportComplex V E F}

/-- Mapping every edge by a transition automorphism preserves path validity. -/
theorem map_path_valid
    (A : TransitionComplexAutomorphism V E F K)
    {startVertex finishVertex : V} {edges : List E}
    (hpath : K.IsEdgePathFrom startVertex edges finishVertex) :
    K.IsEdgePathFrom
      (A.vertexEquiv startVertex) (edges.map A.edgeEquiv)
      (A.vertexEquiv finishVertex) := by
  induction edges generalizing startVertex with
  | nil =>
      change A.vertexEquiv finishVertex = A.vertexEquiv startVertex
      exact congrArg A.vertexEquiv hpath
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      constructor
      · change K.source (A.edgeEquiv e) = A.vertexEquiv startVertex
        rw [A.source_map]
        exact congrArg A.vertexEquiv hsource
      · change K.IsEdgePathFrom
          (K.target (A.edgeEquiv e)) (List.map A.edgeEquiv rest)
          (A.vertexEquiv finishVertex)
        rw [A.target_map]
        exact ih htail

/-- Iterate an automorphism on a finite transition path. -/
def iteratePath
    (A : TransitionComplexAutomorphism V E F K) :
    ℕ → List E → List E
  | 0, edges => edges
  | n + 1, edges => (A.iteratePath n edges).map A.edgeEquiv

/-- A valid path whose endpoints are fixed remains a path with the same
endpoints under every iterate. -/
theorem iteratePath_valid_of_fixed
    (A : TransitionComplexAutomorphism V E F K)
    {startVertex finishVertex : V} {edges : List E}
    (hpath : K.IsEdgePathFrom startVertex edges finishVertex)
    (hstart : A.vertexEquiv startVertex = startVertex)
    (hfinish : A.vertexEquiv finishVertex = finishVertex) :
    ∀ n, K.IsEdgePathFrom startVertex (A.iteratePath n edges) finishVertex := by
  intro n
  induction n with
  | zero =>
      simpa [iteratePath] using hpath
  | succ n ih =>
      have hmapped := A.map_path_valid ih
      simpa [iteratePath, hstart, hfinish] using hmapped

end TransitionComplexAutomorphism

/-- A raw source-equivariant cyclic transition orbit.

The raw edge-source readout and its common-mode face flux are theorem-level
same-section data.  The cyclic transition automorphism reduces the
distinguished `d + 1` path family to one base path; it does not manufacture the
raw source readout from unlabelled transitions. -/
structure SourceEquivariantRawTransitionOrbit
    (d : ℕ) (V E F : Type*) [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  transition : TransitionComplexAutomorphism V E F complex
  atomEquiv : Equiv.Perm (Fin (d + 1))
  rawSource : Fin (d + 1) → E → ℝ
  sourceComponent_map :
    ∀ j e,
      rawSource (atomEquiv j) (transition.edgeEquiv e) =
        rawSource j e
  rawFaceCommonMode :
    ∀ f, ∃ c : ℝ, ∀ j, complex.faceCoboundary (rawSource j) f = c
  startVertex : V
  finishVertex : V
  basePath : List E
  basePathValid :
    complex.IsEdgePathFrom startVertex basePath finishVertex
  startFixed :
    transition.vertexEquiv startVertex = startVertex
  finishFixed :
    transition.vertexEquiv finishVertex = finishVertex
  baseAtom : Fin (d + 1)
  atomOrbit :
    ∀ i, (atomEquiv ^ i.val) baseAtom = i
  rawOffset : Fin (d + 1) → ℝ
  offsetInvariant :
    ∀ n j, rawOffset ((atomEquiv ^ n).symm j) = rawOffset j
  basePathValue :
    ∀ j,
      pathIntegral (rawSource j) basePath =
        rawOffset j + if baseAtom = j then 1 else 0

namespace SourceEquivariantRawTransitionOrbit

variable {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]

/-- The `n`-fold permutation of source atoms. -/
def atomPow
    (O : SourceEquivariantRawTransitionOrbit d V E F) (n : ℕ) :
    Equiv.Perm (Fin (d + 1)) :=
  O.atomEquiv ^ n

/-- The source-indexed path generated from the single base path. -/
def path
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (i : Fin (d + 1)) : List E :=
  O.transition.iteratePath i.val O.basePath

/-- Every generated path retains the registered common endpoints. -/
theorem path_valid
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (i : Fin (d + 1)) :
    O.complex.IsEdgePathFrom O.startVertex (O.path i) O.finishVertex := by
  exact O.transition.iteratePath_valid_of_fixed
    O.basePathValid O.startFixed O.finishFixed i.val

/-- Edge-level source equivariance integrates over a mapped path. -/
theorem mapPath_rawSourcePeriod
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (edges : List E) (j : Fin (d + 1)) :
    pathIntegral (O.rawSource (O.atomEquiv j))
        (edges.map O.transition.edgeEquiv) =
      pathIntegral (O.rawSource j) edges := by
  induction edges with
  | nil =>
      simp [pathIntegral]
  | cons e rest ih =>
      simp [pathIntegral, O.sourceComponent_map, ih]

/-- Source periods are equivariant under every cyclic path iterate. -/
theorem iteratePath_rawSourcePeriod
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (edges : List E) (n : ℕ) (j : Fin (d + 1)) :
    pathIntegral (O.rawSource (O.atomPow n j))
        (O.transition.iteratePath n edges) =
      pathIntegral (O.rawSource j) edges := by
  induction n with
  | zero =>
      simp [atomPow, TransitionComplexAutomorphism.iteratePath]
  | succ n ih =>
      have hatom :
          O.atomPow (n + 1) j =
            O.atomEquiv (O.atomPow n j) := by
        simp [atomPow, pow_succ', Equiv.Perm.mul_apply]
      rw [hatom]
      change pathIntegral
          (O.rawSource (O.atomEquiv (O.atomPow n j)))
          ((O.transition.iteratePath n edges).map
            O.transition.edgeEquiv) =
        pathIntegral (O.rawSource j) edges
      rw [O.mapPath_rawSourcePeriod]
      exact ih

/-- Equivalent component form of iterated raw-source equivariance. -/
theorem iteratePath_rawSourcePeriod_at
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (edges : List E) (n : ℕ) (j : Fin (d + 1)) :
    pathIntegral (O.rawSource j)
        (O.transition.iteratePath n edges) =
      pathIntegral (O.rawSource ((O.atomPow n).symm j)) edges := by
  have h :=
    O.iteratePath_rawSourcePeriod edges n ((O.atomPow n).symm j)
  simpa using h

/-- The generated orbit has the exact raw atomic source periods. -/
theorem path_rawSourcePeriod
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (i j : Fin (d + 1)) :
    pathIntegral (O.rawSource j) (O.path i) =
      O.rawOffset j + if i = j then 1 else 0 := by
  let p := O.atomPow i.val
  calc
    pathIntegral (O.rawSource j) (O.path i) =
        pathIntegral (O.rawSource (p.symm j)) O.basePath := by
          exact O.iteratePath_rawSourcePeriod_at O.basePath i.val j
    _ = O.rawOffset (p.symm j) +
        if O.baseAtom = p.symm j then 1 else 0 :=
          O.basePathValue (p.symm j)
    _ = O.rawOffset j +
        if p O.baseAtom = j then 1 else 0 := by
          have hoffset :
              O.rawOffset (p.symm j) = O.rawOffset j := by
            simpa [p, atomPow] using O.offsetInvariant i.val j
          rw [hoffset]
          by_cases h : p O.baseAtom = j
          · have hb : O.baseAtom = p.symm j := by
              apply p.injective
              simpa using h
            simp [hb]
          · have hb : O.baseAtom ≠ p.symm j := by
              intro hb
              apply h
              rw [hb, p.apply_symm_apply]
            simp [h, hb]
    _ = O.rawOffset j + if i = j then 1 else 0 := by
          have horbit : p O.baseAtom = i := by
            simpa [p, atomPow] using O.atomOrbit i
          rw [horbit]

/-- Distinct source atoms generate distinct paths. -/
theorem path_injective
    (O : SourceEquivariantRawTransitionOrbit d V E F) :
    Function.Injective O.path := by
  intro i k hpath
  apply centeredAtom_injective d
  funext j
  have hi := O.path_rawSourcePeriod i j
  have hk := O.path_rawSourcePeriod k j
  rw [hpath] at hi
  simp only [centeredAtom]
  linarith

/-- Main finite bridge: a source-equivariant raw transition orbit supplies the
raw atomic source-incidence certificate without independently selecting
`d + 1` paths. -/
noncomputable def toRawAtomicSourceIncidenceCertificate
    (O : SourceEquivariantRawTransitionOrbit d V E F) :
    RawAtomicSourceIncidenceCertificate d V E F where
  complex := O.complex
  startVertex := O.startVertex
  finishVertex := O.finishVertex
  path := O.path
  pathValid := O.path_valid
  rawSource := O.rawSource
  rawFaceCommonMode := O.rawFaceCommonMode
  rawOffset := O.rawOffset
  rawPathValue := O.path_rawSourcePeriod

/-- Augmentation projection then supplies the complete source-balanced
confluence certificate. -/
noncomputable def toSourceBalancedConfluenceCertificate
    (O : SourceEquivariantRawTransitionOrbit d V E F) :
    SourceBalancedConfluenceCertificate d V E F :=
  O.toRawAtomicSourceIncidenceCertificate
    |>.toSourceBalancedConfluenceCertificate

/-- The resulting source-period quotient carries the canonical finite carrier
registration used by the simplex and cyclic Noether constructions. -/
noncomputable def finiteSourcePeriodCarrierRegistration
    (O : SourceEquivariantRawTransitionOrbit d V E F) :
    FiniteSourcePeriodCarrierRegistration d :=
  O.toSourceBalancedConfluenceCertificate
    |>.finiteSourcePeriodCarrierRegistration

end SourceEquivariantRawTransitionOrbit

/-- The atomic indicator incidence carried by a finite source-edge frame. -/
noncomputable def sourceEdgeIndicator
    {d : ℕ} {E : Type*}
    (sourceEdge : Fin (d + 1) → E) :
    Fin (d + 1) → E → ℝ := by
  classical
  exact fun j e => if sourceEdge j = e then 1 else 0

/-- A regular orbit of source edges.

This is strictly smaller data than an arbitrary edge-source readout.  The
source-edge frame and its cyclic transition action canonically generate the
raw atomic indicator incidence used below.  The face clause records exactly
the compatibility needed when the registered transition section contains
two-cells; it is vacuous on an orbit-generated one-skeleton. -/
structure RegularSourceEdgeOrbit
    (d : ℕ) (V E F : Type*) [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  transition : TransitionComplexAutomorphism V E F complex
  atomEquiv : Equiv.Perm (Fin (d + 1))
  sourceEdge : Fin (d + 1) → E
  sourceEdge_injective : Function.Injective sourceEdge
  sourceEdge_map :
    ∀ j,
      transition.edgeEquiv (sourceEdge j) =
        sourceEdge (atomEquiv j)
  sourceFaceCommonMode :
    ∀ f, ∃ c : ℝ, ∀ j,
      complex.faceCoboundary (sourceEdgeIndicator sourceEdge j) f = c
  startVertex : V
  finishVertex : V
  tail : List E
  baseAtom : Fin (d + 1)
  basePathValid :
    complex.IsEdgePathFrom
      startVertex (sourceEdge baseAtom :: tail) finishVertex
  tail_avoids_source_edges :
    ∀ j, sourceEdge j ∉ tail
  startFixed :
    transition.vertexEquiv startVertex = startVertex
  finishFixed :
    transition.vertexEquiv finishVertex = finishVertex
  atomOrbit :
    ∀ i, (atomEquiv ^ i.val) baseAtom = i

namespace RegularSourceEdgeOrbit

variable {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]

/-- The canonical raw source readout induced by the regular source-edge
orbit. -/
noncomputable def canonicalRawSource
    (O : RegularSourceEdgeOrbit d V E F) :
    Fin (d + 1) → E → ℝ :=
  sourceEdgeIndicator O.sourceEdge

/-- The induced indicator incidence is equivariant under the registered
transition and source cycles. -/
theorem canonicalRawSource_map
    (O : RegularSourceEdgeOrbit d V E F)
    (j : Fin (d + 1)) (e : E) :
    O.canonicalRawSource (O.atomEquiv j)
        (O.transition.edgeEquiv e) =
      O.canonicalRawSource j e := by
  classical
  by_cases h : O.sourceEdge j = e
  · subst e
    simp [canonicalRawSource, sourceEdgeIndicator, O.sourceEdge_map]
  · have hmap :
        O.sourceEdge (O.atomEquiv j) ≠
          O.transition.edgeEquiv e := by
      intro heq
      apply h
      apply O.transition.edgeEquiv.injective
      calc
        O.transition.edgeEquiv (O.sourceEdge j) =
            O.sourceEdge (O.atomEquiv j) :=
          O.sourceEdge_map j
        _ = O.transition.edgeEquiv e := heq
    simp [canonicalRawSource, sourceEdgeIndicator, h, hmap]

omit [Fintype E] in
/-- An edge list avoiding one source edge has zero period for its indicator
incidence. -/
theorem pathIntegral_sourceEdgeIndicator_eq_zero
    (sourceEdge : Fin (d + 1) → E)
    (j : Fin (d + 1)) (edges : List E)
    (havoid : sourceEdge j ∉ edges) :
    pathIntegral (sourceEdgeIndicator sourceEdge j) edges = 0 := by
  classical
  induction edges with
  | nil =>
      simp [pathIntegral]
  | cons e rest ih =>
      have hhead : sourceEdge j ≠ e := by
        intro heq
        apply havoid
        simp [heq]
      have htail : sourceEdge j ∉ rest := by
        intro hmem
        apply havoid
        simp [hmem]
      rw [pathIntegral, ih htail]
      simp [sourceEdgeIndicator, hhead]

/-- The orbit-generated base path has the raw period of its unique source
edge. -/
theorem basePath_rawSourcePeriod
    (O : RegularSourceEdgeOrbit d V E F)
    (j : Fin (d + 1)) :
    pathIntegral (O.canonicalRawSource j)
        (O.sourceEdge O.baseAtom :: O.tail) =
      if O.baseAtom = j then 1 else 0 := by
  classical
  have htail :
      pathIntegral (O.canonicalRawSource j) O.tail = 0 := by
    exact pathIntegral_sourceEdgeIndicator_eq_zero
      O.sourceEdge j O.tail (O.tail_avoids_source_edges j)
  rw [pathIntegral, htail]
  by_cases h : O.baseAtom = j
  · subst j
    simp [canonicalRawSource, sourceEdgeIndicator]
  · have hedge :
        O.sourceEdge j ≠ O.sourceEdge O.baseAtom := by
      intro heq
      apply h
      exact (O.sourceEdge_injective heq).symm
    simp [canonicalRawSource, sourceEdgeIndicator, h, hedge]

/-- Main constructor: a regular source-edge orbit canonically supplies the
raw source-equivariant transition orbit, so the edge-source readout is no
longer independent input. -/
noncomputable def toSourceEquivariantRawTransitionOrbit
    (O : RegularSourceEdgeOrbit d V E F) :
    SourceEquivariantRawTransitionOrbit d V E F where
  complex := O.complex
  transition := O.transition
  atomEquiv := O.atomEquiv
  rawSource := O.canonicalRawSource
  sourceComponent_map := O.canonicalRawSource_map
  rawFaceCommonMode := O.sourceFaceCommonMode
  startVertex := O.startVertex
  finishVertex := O.finishVertex
  basePath := O.sourceEdge O.baseAtom :: O.tail
  basePathValid := O.basePathValid
  startFixed := O.startFixed
  finishFixed := O.finishFixed
  baseAtom := O.baseAtom
  atomOrbit := O.atomOrbit
  rawOffset := fun _ => 0
  offsetInvariant := by
    intro n j
    rfl
  basePathValue := by
    intro j
    simpa using O.basePath_rawSourcePeriod j

/-- The regular source-edge orbit therefore supplies the complete
source-balanced confluence certificate. -/
noncomputable def toSourceBalancedConfluenceCertificate
    (O : RegularSourceEdgeOrbit d V E F) :
    SourceBalancedConfluenceCertificate d V E F :=
  O.toSourceEquivariantRawTransitionOrbit
    |>.toSourceBalancedConfluenceCertificate

end RegularSourceEdgeOrbit

namespace ConcreteFourCoordinateModel

/-- The four canonical outgoing source edges at the zero event. -/
def initialSourceEdge
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    SigmaFineEdge4 L :=
  forwardEdge (baseState0 L hL) j (by
    simp [baseState0, levelZero, sigmaCoord4Get]
    omega)

@[simp]
theorem initialSourceEdge_source
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    sigmaFineEdgeSource (initialSourceEdge L hL j) =
      baseState0 L hL :=
  rfl

@[simp]
theorem initialSourceEdge_axis
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    sigmaFineEdgeAxis (initialSourceEdge L hL j) = j :=
  rfl

/-- The canonical outgoing source-edge frame is faithful. -/
theorem initialSourceEdge_injective
    (L : ℕ) (hL : 4 ≤ L) :
    Function.Injective (initialSourceEdge L hL) := by
  intro i j h
  have haxis := congrArg sigmaFineEdgeAxis h
  simpa using haxis

/-- The coordinate cycle viewed as an automorphism of the concrete finite
Sigma transition skeleton. -/
noncomputable def rawTransitionComplexAutomorphism
    (L : ℕ) (hL : 4 ≤ L) :
    TransitionComplexAutomorphism
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty
      (sigmaTransitionSkeleton L) where
  vertexEquiv :=
    (transitionAutomorphism L hL).vertexEquiv
  edgeEquiv :=
    (transitionAutomorphism L hL).edgeEquiv
  source_map :=
    (transitionAutomorphism L hL).source_map
  target_map :=
    (transitionAutomorphism L hL).target_map

/-- Coordinate rotation transports the outgoing source-edge frame
equivariantly. -/
theorem rawTransitionComplexAutomorphism_sourceEdge_map
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (rawTransitionComplexAutomorphism L hL).edgeEquiv
        (initialSourceEdge L hL j) =
      initialSourceEdge L hL (axisCycle j) := by
  apply Subtype.ext
  rfl

/-- The later three edges of the base history avoid the outgoing source-edge
frame. -/
theorem initialSourceEdge_not_mem_baseTail
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    initialSourceEdge L hL j ∉
      [baseEdge1 L hL, baseEdge2 L hL, baseEdge3 L hL] := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or]
  constructor
  · intro h
    have hsource := congrArg sigmaFineEdgeSource h
    exact (baseState1_ne_baseState0 L hL) (by simpa using hsource.symm)
  · constructor
    · intro h
      have hsource := congrArg sigmaFineEdgeSource h
      exact (baseState2_ne_baseState0 L hL) (by simpa using hsource.symm)
    · intro h
      have hsource := congrArg sigmaFineEdgeSource h
      exact (baseState3_ne_baseState0 L hL) (by simpa using hsource.symm)

/-- The concrete four-coordinate transition dynamics supply the regular
source-edge orbit from which the raw atomic marking is induced. -/
noncomputable def regularSourceEdgeOrbit
    (L : ℕ) (hL : 4 ≤ L) :
    RegularSourceEdgeOrbit 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty where
  complex := sigmaTransitionSkeleton L
  transition := rawTransitionComplexAutomorphism L hL
  atomEquiv := axisCycle
  sourceEdge := initialSourceEdge L hL
  sourceEdge_injective := initialSourceEdge_injective L hL
  sourceEdge_map :=
    rawTransitionComplexAutomorphism_sourceEdge_map L hL
  sourceFaceCommonMode := by
    intro f
    exact nomatch f
  startVertex := baseState0 L hL
  finishVertex := baseState4 L hL
  tail := [baseEdge1 L hL, baseEdge2 L hL, baseEdge3 L hL]
  baseAtom := 0
  basePathValid := by
    have hsourceEdge :
        initialSourceEdge L hL 0 = baseEdge0 L hL := by
      apply Subtype.ext
      rfl
    simpa [baseHistory, hsourceEdge] using
      (baseHistory L hL).pathValid
  tail_avoids_source_edges :=
    initialSourceEdge_not_mem_baseTail L hL
  startFixed := coordCycle_baseState0 L hL
  finishFixed := coordCycle_baseState4 L hL
  atomOrbit := axisCycle_orbit_zero

/-- The regular source-edge orbit constructs the concrete raw atomic
incidence certificate without taking an arbitrary edge-source map as input. -/
noncomputable def rawAtomicSourceIncidenceCertificateFromSourceEdges
    (L : ℕ) (hL : 4 ≤ L) :
    RawAtomicSourceIncidenceCertificate 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty :=
  (regularSourceEdgeOrbit L hL)
    |>.toSourceEquivariantRawTransitionOrbit
    |>.toRawAtomicSourceIncidenceCertificate

/-- The concrete four-coordinate edge dynamics inhabit the raw
source-equivariant transition-orbit criterion. -/
noncomputable def rawSourceEquivariantTransitionOrbit
    (L : ℕ) (hL : 4 ≤ L) :
    SourceEquivariantRawTransitionOrbit 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty where
  complex := sigmaTransitionSkeleton L
  transition := rawTransitionComplexAutomorphism L hL
  atomEquiv := axisCycle
  rawSource := (rawSourceMarking L hL).component
  sourceComponent_map := rawSourceMarking_equivariant L hL
  rawFaceCommonMode := by
    intro f
    exact nomatch f
  startVertex := baseState0 L hL
  finishVertex := baseState4 L hL
  basePath := (baseHistory L hL).edges
  basePathValid := by
    have hpath := (baseHistory L hL).pathValid
    simpa [baseHistory] using hpath
  startFixed := coordCycle_baseState0 L hL
  finishFixed := coordCycle_baseState4 L hL
  baseAtom := 0
  atomOrbit := axisCycle_orbit_zero
  rawOffset := fun _ => 0
  offsetInvariant := by
    intro n j
    rfl
  basePathValue := by
    intro j
    simpa using rawSourceMarking_baseHistory_period L hL j

/-- The generic orbit constructor recovers a raw atomic incidence certificate
on the actual concrete Sigma transition skeleton. -/
noncomputable def rawAtomicSourceIncidenceCertificateFromOrbit
    (L : ℕ) (hL : 4 ≤ L) :
    RawAtomicSourceIncidenceCertificate 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty :=
  (rawSourceEquivariantTransitionOrbit L hL)
    |>.toRawAtomicSourceIncidenceCertificate

/-- The orbit-generated concrete paths carry the exact four raw source
periods. -/
theorem rawSourceEquivariantTransitionOrbit_path_period
    (L : ℕ) (hL : 4 ≤ L) (i j : Fin 4) :
    pathIntegral ((rawSourceMarking L hL).component j)
        ((rawSourceEquivariantTransitionOrbit L hL).path i) =
      if i = j then 1 else 0 := by
  simpa [rawSourceEquivariantTransitionOrbit] using
    (rawSourceEquivariantTransitionOrbit L hL).path_rawSourcePeriod i j

end ConcreteFourCoordinateModel

end SourceConfluence
end Hardtest
