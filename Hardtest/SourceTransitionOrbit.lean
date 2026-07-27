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

The final criterion in this module separates orbit generation from
completeness.  A source-preserving transition automorphism and one seed edge
generate `d + 1` distinct outgoing edges, while an independently established
local valence bound rules out additional outgoing edges.  Finite cardinality
then constructs the complete regular cyclic outgoing star.

An exact finite transition-complex equivalence provides the application-level
transport theorem.  It conjugates the canonical vertex, edge, and face
automorphisms; carries the complete outgoing star to the registered
same-section complex; and transports paths, raw source cochains, path periods,
and face coboundaries.  The theorem does not infer such an equivalence from
geometric readout data.
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
  faceEquiv : Equiv.Perm F
  source_map :
    ∀ e, K.source (edgeEquiv e) = vertexEquiv (K.source e)
  target_map :
    ∀ e, K.target (edgeEquiv e) = vertexEquiv (K.target e)
  faceBoundary_map :
    ∀ f e,
      K.faceBoundary (faceEquiv f) (edgeEquiv e) =
        K.faceBoundary f e

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

/-- Iterating a transition automorphism transports the source vertex by the
same number of vertex-automorphism steps. -/
theorem iterateEdge_source
    (A : TransitionComplexAutomorphism V E F K)
    (n : ℕ) (e : E) :
    K.source ((A.edgeEquiv ^ n) e) =
      (A.vertexEquiv ^ n) (K.source e) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [A.source_map, ih]

/-- Every iterate of an edge leaving a fixed vertex leaves that same vertex. -/
theorem iterateEdge_source_of_fixed
    (A : TransitionComplexAutomorphism V E F K)
    (n : ℕ) (e : E) (v : V)
    (hsource : K.source e = v)
    (hfixed : A.vertexEquiv v = v) :
    K.source ((A.edgeEquiv ^ n) e) = v := by
  rw [A.iterateEdge_source, hsource]
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [ih, hfixed]

end TransitionComplexAutomorphism

/-- The complete outgoing edge star of a vertex in a finite transition
complex. -/
abbrev OutgoingEdge
    {V E F : Type*} [Fintype E] [Fintype F]
    (K : FiniteTransportComplex V E F) (v : V) :=
  {e : E // K.source e = v}

/--
An intrinsic complete regular cyclic outgoing star.

This criterion contains no independent source-atom labelling.  A single base
edge and the registered transition automorphism enumerate every outgoing edge
exactly once during the first `d + 1` iterates.  The TeX result in
`discrete_noether_sigma_v3.tex` quotients the remaining base-edge choice by
simultaneous cyclic relabelling before coupling this star to the regular source
atoms.
-/
structure CompleteRegularCyclicOutgoingStar
    (d : ℕ) (V E F : Type*) [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  transition : TransitionComplexAutomorphism V E F complex
  startVertex : V
  startFixed :
    transition.vertexEquiv startVertex = startVertex
  baseEdge : E
  baseEdge_source :
    complex.source baseEdge = startVertex
  orbit_complete :
    ∀ e, complex.source e = startVertex →
      ∃! i : Fin (d + 1),
        (transition.edgeEquiv ^ i.val) baseEdge = e

namespace CompleteRegularCyclicOutgoingStar

variable {d : ℕ} {V E F : Type*} [Fintype E] [Fintype F]

/-- The cyclic enumeration induced by the base edge and transition action. -/
def sourceEdge
    (S : CompleteRegularCyclicOutgoingStar d V E F)
    (i : Fin (d + 1)) : E :=
  (S.transition.edgeEquiv ^ i.val) S.baseEdge

/-- Every cyclically enumerated edge belongs to the registered outgoing star. -/
theorem sourceEdge_source
    (S : CompleteRegularCyclicOutgoingStar d V E F)
    (i : Fin (d + 1)) :
    S.complex.source (S.sourceEdge i) = S.startVertex := by
  exact S.transition.iterateEdge_source_of_fixed
    i.val S.baseEdge S.startVertex S.baseEdge_source S.startFixed

/-- The first `d + 1` cyclic iterates are pairwise distinct. -/
theorem sourceEdge_injective
    (S : CompleteRegularCyclicOutgoingStar d V E F) :
    Function.Injective S.sourceEdge := by
  intro i j hij
  rcases S.orbit_complete (S.sourceEdge i) (S.sourceEdge_source i) with
    ⟨k, hk, hunique⟩
  have hi : i = k := hunique i rfl
  have hj : j = k := hunique j hij.symm
  exact hi.trans hj.symm

/-- Every outgoing edge occurs in the cyclic enumeration. -/
theorem sourceEdge_surjective
    (S : CompleteRegularCyclicOutgoingStar d V E F) :
    Function.Surjective
      (fun i : Fin (d + 1) =>
        (⟨S.sourceEdge i, S.sourceEdge_source i⟩ :
          OutgoingEdge S.complex S.startVertex)) := by
  intro e
  rcases S.orbit_complete e.1 e.2 with ⟨i, hi, _⟩
  refine ⟨i, ?_⟩
  apply Subtype.ext
  exact hi

/--
The source-axis index is equivalent to the complete outgoing star.  Thus the
cyclic frame is not a selected proper subset of that star.
-/
noncomputable def sourceEdgeEquiv
    (S : CompleteRegularCyclicOutgoingStar d V E F) :
    Fin (d + 1) ≃ OutgoingEdge S.complex S.startVertex :=
  Equiv.ofBijective
    (fun i =>
      (⟨S.sourceEdge i, S.sourceEdge_source i⟩ :
        OutgoingEdge S.complex S.startVertex))
    ⟨by
      intro i j hij
      apply S.sourceEdge_injective
      exact congrArg Subtype.val hij,
      S.sourceEdge_surjective⟩

/--
Every possible base edge of the outgoing star is a unique cyclic shift of the
registered base edge.  This is the finite base-gauge statement used by the
paper-facing quotient construction.
-/
theorem outgoingEdge_unique_cyclic_shift
    (S : CompleteRegularCyclicOutgoingStar d V E F)
    (e : OutgoingEdge S.complex S.startVertex) :
    ∃! i : Fin (d + 1), S.sourceEdge i = e.1 :=
  S.orbit_complete e.1 e.2

end CompleteRegularCyclicOutgoingStar

/--
A cyclic outgoing orbit together with an independent local valence bound.

The orbit data provide `d + 1` distinct admissible outgoing edges.  The
cardinality bound concerns the complete outgoing star, not the chosen orbit,
so it is an independent finite exhaustion certificate rather than a restatement
of orbit completeness.  The paper-facing counterpart is the
valence-bounded equivariant admissibility criterion in
`discrete_noether_sigma_v3.tex`.
-/
structure ValenceBoundedCyclicOutgoingOrbit
    (d : ℕ) (V E F : Type*) [DecidableEq V] [Fintype E] [Fintype F] where
  complex : FiniteTransportComplex V E F
  transition : TransitionComplexAutomorphism V E F complex
  startVertex : V
  startFixed :
    transition.vertexEquiv startVertex = startVertex
  baseEdge : E
  baseEdge_source :
    complex.source baseEdge = startVertex
  orbit_injective :
    Function.Injective
      (fun i : Fin (d + 1) =>
        (transition.edgeEquiv ^ i.val) baseEdge)
  outgoing_card_le :
    Fintype.card (OutgoingEdge complex startVertex) ≤ d + 1

namespace ValenceBoundedCyclicOutgoingOrbit

variable {d : ℕ} {V E F : Type*} [DecidableEq V] [Fintype E] [Fintype F]

/-- The cyclic seed orbit, typed in the complete outgoing star. -/
def sourceEdge
    (O : ValenceBoundedCyclicOutgoingOrbit d V E F)
    (i : Fin (d + 1)) :
    OutgoingEdge O.complex O.startVertex :=
  ⟨(O.transition.edgeEquiv ^ i.val) O.baseEdge,
    O.transition.iterateEdge_source_of_fixed
      i.val O.baseEdge O.startVertex O.baseEdge_source O.startFixed⟩

/-- Distinct orbit indices give distinct outgoing edges. -/
theorem sourceEdge_injective
    (O : ValenceBoundedCyclicOutgoingOrbit d V E F) :
    Function.Injective O.sourceEdge := by
  intro i j hij
  apply O.orbit_injective
  exact congrArg Subtype.val hij

/--
The complete outgoing star has exactly `d + 1` edges.  The lower bound comes
from the injective cyclic orbit; the upper bound is the independent local
valence certificate.
-/
theorem outgoing_card_eq
    (O : ValenceBoundedCyclicOutgoingOrbit d V E F) :
    Fintype.card (OutgoingEdge O.complex O.startVertex) = d + 1 := by
  apply Nat.le_antisymm O.outgoing_card_le
  simpa using Fintype.card_le_of_injective O.sourceEdge O.sourceEdge_injective

/-- The cyclic seed orbit exhausts the complete outgoing star. -/
theorem sourceEdge_bijective
    (O : ValenceBoundedCyclicOutgoingOrbit d V E F) :
    Function.Bijective O.sourceEdge := by
  apply (Fintype.bijective_iff_injective_and_card O.sourceEdge).2
  refine ⟨O.sourceEdge_injective, ?_⟩
  rw [Fintype.card_fin, O.outgoing_card_eq]

/--
An injective cyclic seed orbit and the independent valence bound canonically
construct an intrinsic complete regular cyclic outgoing star.
-/
def toCompleteRegularCyclicOutgoingStar
    (O : ValenceBoundedCyclicOutgoingOrbit d V E F) :
    CompleteRegularCyclicOutgoingStar d V E F where
  complex := O.complex
  transition := O.transition
  startVertex := O.startVertex
  startFixed := O.startFixed
  baseEdge := O.baseEdge
  baseEdge_source := O.baseEdge_source
  orbit_complete := by
    intro e he
    let outgoing : OutgoingEdge O.complex O.startVertex := ⟨e, he⟩
    rcases O.sourceEdge_bijective.2 outgoing with ⟨i, hi⟩
    refine ⟨i, congrArg Subtype.val hi, ?_⟩
    intro j hj
    apply O.sourceEdge_injective
    apply Subtype.ext
    exact hj.trans (congrArg Subtype.val hi).symm

end ValenceBoundedCyclicOutgoingOrbit

/--
An exact equivalence between two finite transition complexes.

The vertex, edge, and face equivalences preserve the directed incidence and
the integral face-boundary coefficients.  In the paper-facing criterion this
is the finite same-section registration datum: it is strong enough to
transport a proved transition-star realization, but it is not inferred from a
static geometric readout.
-/
structure TransitionComplexEquiv
    (V E F V' E' F' : Type*)
    [Fintype E] [Fintype F] [Fintype E'] [Fintype F']
    (K : FiniteTransportComplex V E F)
    (K' : FiniteTransportComplex V' E' F') where
  vertexEquiv : V ≃ V'
  edgeEquiv : E ≃ E'
  faceEquiv : F ≃ F'
  source_map :
    ∀ e, K'.source (edgeEquiv e) = vertexEquiv (K.source e)
  target_map :
    ∀ e, K'.target (edgeEquiv e) = vertexEquiv (K.target e)
  faceBoundary_map :
    ∀ f e,
      K'.faceBoundary (faceEquiv f) (edgeEquiv e) =
        K.faceBoundary f e

namespace TransitionComplexEquiv

variable {d : ℕ}
  {V E F V' E' F' : Type*}
  [Fintype E] [Fintype F] [Fintype E'] [Fintype F']
  {K : FiniteTransportComplex V E F}
  {K' : FiniteTransportComplex V' E' F'}

/-- Map an edge list across an exact transition-complex equivalence. -/
def mapPath
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (edges : List E) : List E' :=
  edges.map I.edgeEquiv

/-- Mapping every edge by an exact complex equivalence preserves path validity
and transports both endpoints by the vertex equivalence. -/
theorem mapPath_valid
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    {startVertex finishVertex : V} {edges : List E}
    (hpath : K.IsEdgePathFrom startVertex edges finishVertex) :
    K'.IsEdgePathFrom
      (I.vertexEquiv startVertex) (I.mapPath edges)
      (I.vertexEquiv finishVertex) := by
  induction edges generalizing startVertex with
  | nil =>
      change I.vertexEquiv finishVertex = I.vertexEquiv startVertex
      exact congrArg I.vertexEquiv hpath
  | cons e rest ih =>
      rcases hpath with ⟨hsource, htail⟩
      constructor
      · change K'.source (I.edgeEquiv e) = I.vertexEquiv startVertex
        rw [I.source_map]
        exact congrArg I.vertexEquiv hsource
      · change K'.IsEdgePathFrom
          (K'.target (I.edgeEquiv e)) (I.mapPath rest)
          (I.vertexEquiv finishVertex)
        rw [I.target_map]
        exact ih htail

/-- Pull an edge cochain forward by precomposition with the inverse edge
equivalence. -/
def mapCochain
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (rho : E → ℝ) : E' → ℝ :=
  fun e' => rho (I.edgeEquiv.symm e')

@[simp]
theorem mapCochain_edge_apply
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (rho : E → ℝ) (e : E) :
    I.mapCochain rho (I.edgeEquiv e) = rho e := by
  simp [mapCochain]

/-- Reindexing a path and its cochain by the same edge equivalence preserves
the finite path integral exactly. -/
theorem pathIntegral_mapPath
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (rho : E → ℝ) (edges : List E) :
    pathIntegral (I.mapCochain rho) (I.mapPath edges) =
      pathIntegral rho edges := by
  induction edges with
  | nil =>
      simp [mapPath, pathIntegral]
  | cons e rest ih =>
      change
        I.mapCochain rho (I.edgeEquiv e) +
            pathIntegral (I.mapCochain rho) (I.mapPath rest) =
          rho e + pathIntegral rho rest
      rw [I.mapCochain_edge_apply, ih]

/-- Face coboundaries are invariant under the simultaneous face, edge, and
cochain transport of an exact transition-complex equivalence. -/
theorem faceCoboundary_mapCochain
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (rho : E → ℝ) (f : F) :
    K'.faceCoboundary (I.mapCochain rho) (I.faceEquiv f) =
      K.faceCoboundary rho f := by
  unfold FiniteTransportComplex.faceCoboundary
  calc
    (∑ e' : E',
        (K'.faceBoundary (I.faceEquiv f) e' : ℝ) *
          I.mapCochain rho e') =
        ∑ e : E,
          (K'.faceBoundary (I.faceEquiv f) (I.edgeEquiv e) : ℝ) *
            I.mapCochain rho (I.edgeEquiv e) := by
              symm
              exact I.edgeEquiv.sum_comp
                (fun e' : E' =>
                  (K'.faceBoundary (I.faceEquiv f) e' : ℝ) *
                    I.mapCochain rho e')
    _ = ∑ e : E, (K.faceBoundary f e : ℝ) * rho e := by
          simp [I.faceBoundary_map]

/--
Conjugating a transition automorphism by a complex equivalence constructs the
corresponding automorphism on the registered transition complex.
-/
noncomputable def mapAutomorphism
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (A : TransitionComplexAutomorphism V E F K) :
    TransitionComplexAutomorphism V' E' F' K' where
  vertexEquiv :=
    (I.vertexEquiv.symm.trans A.vertexEquiv).trans I.vertexEquiv
  edgeEquiv :=
    (I.edgeEquiv.symm.trans A.edgeEquiv).trans I.edgeEquiv
  faceEquiv :=
    (I.faceEquiv.symm.trans A.faceEquiv).trans I.faceEquiv
  source_map := by
    intro e'
    have hs :
        K.source (I.edgeEquiv.symm e') =
          I.vertexEquiv.symm (K'.source e') := by
      apply I.vertexEquiv.injective
      simpa using (I.source_map (I.edgeEquiv.symm e')).symm
    simp only [Equiv.trans_apply]
    rw [I.source_map, A.source_map, hs]
  target_map := by
    intro e'
    have ht :
        K.target (I.edgeEquiv.symm e') =
          I.vertexEquiv.symm (K'.target e') := by
      apply I.vertexEquiv.injective
      simpa using (I.target_map (I.edgeEquiv.symm e')).symm
    simp only [Equiv.trans_apply]
    rw [I.target_map, A.target_map, ht]
  faceBoundary_map := by
    intro f' e'
    simp only [Equiv.trans_apply]
    calc
      K'.faceBoundary
          (I.faceEquiv (A.faceEquiv (I.faceEquiv.symm f')))
          (I.edgeEquiv (A.edgeEquiv (I.edgeEquiv.symm e'))) =
          K.faceBoundary
            (A.faceEquiv (I.faceEquiv.symm f'))
            (A.edgeEquiv (I.edgeEquiv.symm e')) :=
        I.faceBoundary_map _ _
      _ = K.faceBoundary
            (I.faceEquiv.symm f') (I.edgeEquiv.symm e') :=
        A.faceBoundary_map _ _
      _ = K'.faceBoundary f' e' := by
        simpa using
          (I.faceBoundary_map
            (I.faceEquiv.symm f') (I.edgeEquiv.symm e')).symm

@[simp]
theorem mapAutomorphism_vertex_apply
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (A : TransitionComplexAutomorphism V E F K)
    (v : V) :
    (I.mapAutomorphism A).vertexEquiv (I.vertexEquiv v) =
      I.vertexEquiv (A.vertexEquiv v) := by
  simp [mapAutomorphism]

@[simp]
theorem mapAutomorphism_edge_apply
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (A : TransitionComplexAutomorphism V E F K)
    (e : E) :
    (I.mapAutomorphism A).edgeEquiv (I.edgeEquiv e) =
      I.edgeEquiv (A.edgeEquiv e) := by
  simp [mapAutomorphism]

@[simp]
theorem mapAutomorphism_face_apply
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (A : TransitionComplexAutomorphism V E F K)
    (f : F) :
    (I.mapAutomorphism A).faceEquiv (I.faceEquiv f) =
      I.faceEquiv (A.faceEquiv f) := by
  simp [mapAutomorphism]

/-- Conjugation intertwines every finite iterate of the edge action. -/
theorem mapAutomorphism_edge_pow_apply
    (I : TransitionComplexEquiv V E F V' E' F' K K')
    (A : TransitionComplexAutomorphism V E F K)
    (n : ℕ) (e : E) :
    ((I.mapAutomorphism A).edgeEquiv ^ n) (I.edgeEquiv e) =
      I.edgeEquiv ((A.edgeEquiv ^ n) e) := by
  induction n with
  | zero =>
      simp
  | succ n ih =>
      simp only [pow_succ', Equiv.Perm.mul_apply]
      rw [ih, I.mapAutomorphism_edge_apply]

/--
An exact same-section transition-complex equivalence transports a complete
regular cyclic outgoing star.  The physical transition automorphism is the
conjugate of the supplied Sigma automorphism; no independent edge relabeling
is introduced.
-/
noncomputable def mapCompleteRegularCyclicOutgoingStar
    (S : CompleteRegularCyclicOutgoingStar d V E F)
    (I : TransitionComplexEquiv V E F V' E' F' S.complex K') :
    CompleteRegularCyclicOutgoingStar d V' E' F' where
  complex := K'
  transition := I.mapAutomorphism S.transition
  startVertex := I.vertexEquiv S.startVertex
  startFixed := by
    rw [I.mapAutomorphism_vertex_apply, S.startFixed]
  baseEdge := I.edgeEquiv S.baseEdge
  baseEdge_source := by
    rw [I.source_map, S.baseEdge_source]
  orbit_complete := by
    intro e' he'
    let e : E := I.edgeEquiv.symm e'
    have he : S.complex.source e = S.startVertex := by
      have hs := I.source_map e
      have hie : I.edgeEquiv e = e' := I.edgeEquiv.apply_symm_apply e'
      rw [hie, he'] at hs
      exact (I.vertexEquiv.injective hs.symm)
    rcases S.orbit_complete e he with ⟨i, hi, hunique⟩
    refine ⟨i, ?_, ?_⟩
    · change
        ((I.mapAutomorphism S.transition).edgeEquiv ^ i.val)
            (I.edgeEquiv S.baseEdge) = e'
      rw [I.mapAutomorphism_edge_pow_apply, hi]
      exact I.edgeEquiv.apply_symm_apply e'
    · intro j hj
      apply hunique
      apply I.edgeEquiv.injective
      calc
        I.edgeEquiv ((S.transition.edgeEquiv ^ j.val) S.baseEdge) =
            ((I.mapAutomorphism S.transition).edgeEquiv ^ j.val)
              (I.edgeEquiv S.baseEdge) :=
          (I.mapAutomorphism_edge_pow_apply
            S.transition j.val S.baseEdge).symm
        _ = e' := hj
        _ = I.edgeEquiv e := (I.edgeEquiv.apply_symm_apply e').symm

end TransitionComplexEquiv

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

/--
An exact transition-complex equivalence transports the complete
source-equivariant raw transition package.  Paths and raw source cochains are
reindexed by the edge equivalence; path periods and face coboundaries are
therefore preserved rather than re-assumed on the target complex.
-/
noncomputable def mapTransitionComplexEquiv
    {V' E' F' : Type*} [Fintype E'] [Fintype F']
    {K' : FiniteTransportComplex V' E' F'}
    (O : SourceEquivariantRawTransitionOrbit d V E F)
    (I : TransitionComplexEquiv
      V E F V' E' F' O.complex K') :
    SourceEquivariantRawTransitionOrbit d V' E' F' where
  complex := K'
  transition := I.mapAutomorphism O.transition
  atomEquiv := O.atomEquiv
  rawSource := fun j => I.mapCochain (O.rawSource j)
  sourceComponent_map := by
    intro j e'
    simp [TransitionComplexEquiv.mapCochain,
      TransitionComplexEquiv.mapAutomorphism, O.sourceComponent_map]
  rawFaceCommonMode := by
    intro f'
    let f := I.faceEquiv.symm f'
    rcases O.rawFaceCommonMode f with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    intro j
    have hface :
        I.faceEquiv f = f' := I.faceEquiv.apply_symm_apply f'
    rw [← hface, I.faceCoboundary_mapCochain]
    exact hc j
  startVertex := I.vertexEquiv O.startVertex
  finishVertex := I.vertexEquiv O.finishVertex
  basePath := I.mapPath O.basePath
  basePathValid := I.mapPath_valid O.basePathValid
  startFixed := by
    rw [I.mapAutomorphism_vertex_apply, O.startFixed]
  finishFixed := by
    rw [I.mapAutomorphism_vertex_apply, O.finishFixed]
  baseAtom := O.baseAtom
  atomOrbit := O.atomOrbit
  rawOffset := O.rawOffset
  offsetInvariant := O.offsetInvariant
  basePathValue := by
    intro j
    rw [I.pathIntegral_mapPath]
    exact O.basePathValue j

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

/--
Every admissible fine edge leaving the zero event is forward.  This is the
finite transition-level use of the boundary state: a backward edge at level
zero would violate `SigmaFineEdgeValid4`.
-/
theorem edge_from_baseState0_forward
    (L : ℕ) (hL : 4 ≤ L) (e : SigmaFineEdge4 L)
    (hsource :
      sigmaFineEdgeSource e = baseState0 L hL) :
    sigmaFineEdgeForward e = true := by
  by_contra hforward
  have hfalse : sigmaFineEdgeForward e = false :=
    Bool.eq_false_of_not_eq_true hforward
  have hraw : e.1.2 = false := by
    simpa [sigmaFineEdgeForward] using hfalse
  have hpositive :
      0 <
        (sigmaCoord4Get
          (sigmaFineEdgeSource e)
          (sigmaFineEdgeAxis e)).val := by
    simpa [SigmaFineEdgeValid4, sigmaFineEdgeForward, hraw] using e.2
  rw [hsource] at hpositive
  simp [baseState0, levelZero, sigmaCoord4Get] at hpositive

/--
The four canonical source edges exhaust the full admissible outgoing star at
the zero event.  Thus the edge frame is not a proper selected subset of that
star.
-/
theorem edge_eq_initialSourceEdge_of_source_eq
    (L : ℕ) (hL : 4 ≤ L) (e : SigmaFineEdge4 L)
    (hsource :
      sigmaFineEdgeSource e = baseState0 L hL) :
    e = initialSourceEdge L hL (sigmaFineEdgeAxis e) := by
  apply Subtype.ext
  change
    ((sigmaFineEdgeSource e, sigmaFineEdgeAxis e),
        sigmaFineEdgeForward e) =
      ((baseState0 L hL, sigmaFineEdgeAxis e), true)
  rw [hsource, edge_from_baseState0_forward L hL e hsource]

/-- The complete admissible outgoing star at the zero event. -/
abbrev InitialOutgoingEdge
    (L : ℕ) (hL : 4 ≤ L) :=
  {e : SigmaFineEdge4 L //
    sigmaFineEdgeSource e = baseState0 L hL}

/--
The source-axis index is canonically equivalent to the complete outgoing
transition star at the zero event.
-/
def initialSourceEdgeEquiv
    (L : ℕ) (hL : 4 ≤ L) :
    Fin 4 ≃ InitialOutgoingEdge L hL where
  toFun j :=
    ⟨initialSourceEdge L hL j, initialSourceEdge_source L hL j⟩
  invFun e := sigmaFineEdgeAxis e.1
  left_inv := by
    intro j
    exact initialSourceEdge_axis L hL j
  right_inv := by
    intro e
    apply Subtype.ext
    exact
      (edge_eq_initialSourceEdge_of_source_eq
        L hL e.1 e.2).symm

@[simp]
theorem initialSourceEdge_primitiveTime
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    sigmaPlanckPrimitiveTime4 (initialSourceEdge L hL j) = 1 :=
  sigmaPlanckPrimitiveTime4_eq_one _

@[simp]
theorem initialSourceEdge_tension
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (concreteSigmaAdmissibleDynamics4 L hL).tension
        (initialSourceEdge L hL j) =
      1 := by
  rfl

theorem initialSourceEdge_tension_pos
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    0 <
      (concreteSigmaAdmissibleDynamics4 L hL).tension
        (initialSourceEdge L hL j) := by
  rw [initialSourceEdge_tension]
  norm_num

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
  faceEquiv :=
    Equiv.refl Empty
  source_map :=
    (transitionAutomorphism L hL).source_map
  target_map :=
    (transitionAutomorphism L hL).target_map
  faceBoundary_map := by
    intro f
    exact nomatch f

/-- Coordinate rotation transports the outgoing source-edge frame
equivariantly. -/
theorem rawTransitionComplexAutomorphism_sourceEdge_map
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    (rawTransitionComplexAutomorphism L hL).edgeEquiv
        (initialSourceEdge L hL j) =
      initialSourceEdge L hL (axisCycle j) := by
  apply Subtype.ext
  rfl

/-- Iterating coordinate rotation from axis zero enumerates the complete
canonical source-edge frame. -/
theorem rawTransitionComplexAutomorphism_sourceEdge_orbit
    (L : ℕ) (hL : 4 ≤ L) (j : Fin 4) :
    ((rawTransitionComplexAutomorphism L hL).edgeEquiv ^ j.val)
        (initialSourceEdge L hL 0) =
      initialSourceEdge L hL j := by
  fin_cases j <;> apply Subtype.ext <;> rfl

/--
The coordinate-cycle orbit and the independently proved four-edge valence
bound inhabit the generic valence-bounded criterion.
-/
noncomputable def valenceBoundedCyclicOutgoingOrbit
    (L : ℕ) (hL : 4 ≤ L) :
    ValenceBoundedCyclicOutgoingOrbit 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty where
  complex := sigmaTransitionSkeleton L
  transition := rawTransitionComplexAutomorphism L hL
  startVertex := baseState0 L hL
  startFixed := coordCycle_baseState0 L hL
  baseEdge := initialSourceEdge L hL 0
  baseEdge_source := initialSourceEdge_source L hL 0
  orbit_injective := by
    intro i j hij
    change
      ((rawTransitionComplexAutomorphism L hL).edgeEquiv ^ i.val)
          (initialSourceEdge L hL 0) =
        ((rawTransitionComplexAutomorphism L hL).edgeEquiv ^ j.val)
          (initialSourceEdge L hL 0) at hij
    rw [rawTransitionComplexAutomorphism_sourceEdge_orbit,
      rawTransitionComplexAutomorphism_sourceEdge_orbit] at hij
    exact initialSourceEdge_injective L hL hij
  outgoing_card_le := by
    have hcard :
        Fintype.card (InitialOutgoingEdge L hL) = 4 := by
      simpa using (Fintype.card_congr (initialSourceEdgeEquiv L hL)).symm
    exact hcard.le

/--
The concrete zero event satisfies the intrinsic complete regular cyclic
outgoing-star criterion through the valence-bounded constructor.  In
particular, the source-axis frame is recovered from the transition action, one
base edge, and the independently verified complete-star cardinality.
-/
noncomputable def completeRegularCyclicOutgoingStar
    (L : ℕ) (hL : 4 ≤ L) :
    CompleteRegularCyclicOutgoingStar 3
      (SigmaCoord4 L) (SigmaFineEdge4 L) Empty :=
  (valenceBoundedCyclicOutgoingOrbit L hL)
    |>.toCompleteRegularCyclicOutgoingStar

/-- The generic intrinsic-star equivalence recovers the complete concrete
outgoing star at the zero event. -/
noncomputable def intrinsicInitialSourceEdgeEquiv
    (L : ℕ) (hL : 4 ≤ L) :
    Fin 4 ≃ InitialOutgoingEdge L hL :=
  (completeRegularCyclicOutgoingStar L hL).sourceEdgeEquiv

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
