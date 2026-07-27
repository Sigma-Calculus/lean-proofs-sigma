# Sigma Lean Proof Pool

This Lake project is the persistent Lean proof pool for finalized sigma proof modules.
It is intended to be reusable by later Lean formalizations via normal Lean imports.

## Clone

```bash
git clone https://github.com/Sigma-Calculus/lean-proofs-sigma.git
cd lean-proofs-sigma
```

## Canonical Modules

- `Hardtest.BlockLaplacian`
  - File: `Hardtest/BlockLaplacian.lean`
  - Source paper context: Appendix VI Planck/no-zero source bridge,
    block Laplacian, and spectral program.

- `Hardtest.SigmaAxioms`
  - File: `Hardtest/SigmaAxioms.lean`
  - Source paper context: Appendix VI joint finite transition-level model for
    `sigma.P` and `sigma.1`--`sigma.7`, generated from an admissible finite
    Sigma dynamics class.

- `Hardtest.SigmaRegge`
  - File: `Hardtest/SigmaRegge.lean`
  - Source paper context: Appendix VI sigma-Regge curvature readout,
    finite-template shape-regularity source, vertex/hinge identity,
    conditional continuum bridge, and open-curvature coefficient normalization.

- `Hardtest.HorizonReadout`
  - File: `Hardtest/HorizonReadout.lean`
  - Source paper context: Appendix VI finite horizon readout separation,
    residual completion, and external thermodynamic readout incompleteness.

- `Hardtest.HorizonRadiationVisibility`
  - File: `Hardtest/HorizonRadiationVisibility.lean`
  - Source paper context: Appendix VI horizon-to-radiation visibility
    criterion: kernel-exact radiation readout induces an injective reduced
    horizon quotient readout.

- `Hardtest.PatchVisibility`
  - File: `Hardtest/PatchVisibility.lean`
  - Source paper context: finite Sigma patch visibility thresholds: Planck-clock
    temporal support, representative/readout stability, collapse action, and
    logarithmic external visibility threshold.

- `Hardtest.GaugeTransport`
  - File: `Hardtest/GaugeTransport.lean`
  - Source paper context: gauge-like transport, local exactness, cube/Bianchi core,
    finite plaquette algebra, and reduced holonomy Noether core.

- `Hardtest.SourceConfluence`
  - File: `Hardtest/SourceConfluence.lean`
  - Source paper context: the source-balanced confluence theorem in
    `discrete_noether_sigma_v3.tex` and its use by
    `Sigma_Finite_Line_Carrier_Tetrahedral_Stability_Criterion_full_proof.tex`;
    finite parallel-channel confluence, augmentation-null rank-`d`
    certificate, positive Sigma transition histories, and their construction
    from one source-equivariant cyclic history orbit.  The
    `ConcreteFourCoordinateModel` namespace additionally realizes the
    rank-three certificate using actual positive fine-edge histories in the
    concrete four-coordinate Sigma dynamics.  The source-period quotient
    identifies same-endpoint histories exactly when every registered source
    period agrees and proves the universal factorization of period-invariant
    readouts.  Its finite carrier-registration interface proves that the
    distinguished period classes have exact augmentation rank and the canonical
    simplex Gram matrix without selecting path representatives.  Simultaneous
    relabeling of the distinguished classes and source components preserves
    the registration and Gram certificate, so absolute source-atom names are
    not part of the carrier payload.  A raw atomic source-incidence constructor
    additionally projects common-mode transition incidence to the closed
    augmentation-null source cochain required by the confluence theorem.  The
    concrete four-coordinate model constructs this raw incidence on actual
    Sigma fine-edge histories and proves that its augmentation projection is
    exactly the centered source marking.  On the complete domain of positive
    histories from the common zero state to the common unit state, it proves
    that the raw period is determined exactly by the first source axis and
    that the resulting quotient has precisely four intrinsic period classes.
    The cyclic histories are therefore representatives rather than an
    additional class selection.  The module also constructs the maximal
    source-admissible face hull and proves that distinct source-history
    comparison loops either remain non-boundaries or force nonzero source flux
    through any proposed filling.
  - Scope: the source-generated coordinate model is constructive.  An
    independently prescribed physical transition network still requires a
    same-section identification, up to simultaneous source relabeling, of its
    positive history domain and raw atomic source-period quotient with the
    canonical four-class quotient, together with its source-admissible face
    hull.  An exact state potential alone cannot supply distinct same-endpoint
    source periods.

- `Hardtest.DiscreteNoether`
  - File: `Hardtest/DiscreteNoether.lean`
  - Source paper context: finite reduced-holonomy Noether charge,
    model-independent cyclic conservation, and functorial isometric transport.

- `Hardtest.SourceNoether`
  - File: `Hardtest/SourceNoether.lean`
  - Source paper context: canonical rank-three source-generated realization of
    the non-scalar cyclic harmonic/Noether action in
    `discrete_noether_sigma_v3.tex`.  The four-source cyclic transition
    restricts to an orthogonal order-four action on the augmentation-null
    carrier, produces cyclic reduced Noether data, and has a directional
    charge that is not a scalar multiple of the carrier norm.
  - Scope: this closes the formal source-to-Noether bridge for the canonical
    parallel-channel response model.  It does not identify an independently
    prescribed physical transition network with that model.

- `Hardtest.YangMills`
  - File: `Hardtest/YangMills.lean`
  - Source paper context: finite sigma-induced gauge transport, closed-loop
    frame invariance, finite cube/Bianchi identity, and matrix plaquette
    curvature core.

- `Hardtest.YangMillsContinuumBridge`
  - File: `Hardtest/YangMillsContinuumBridge.lean`
  - Source paper context: explicit continuum bridge hypotheses for smooth
    representative completion, controlled plaquette expansion, leading
    EFT classification, and the conditional Yang--Mills leading-term conclusion.

## Build Commands

Run from the repository root:

```bash
lake build Hardtest.BlockLaplacian
lake build Hardtest.SigmaAxioms
lake build Hardtest.SigmaRegge
lake build Hardtest.HorizonReadout
lake build Hardtest.HorizonRadiationVisibility
lake build Hardtest.PatchVisibility
lake build Hardtest.GaugeTransport
lake build Hardtest.SourceConfluence
lake build Hardtest.DiscreteNoether
lake build Hardtest.SourceNoether
lake build Hardtest.YangMills
lake build Hardtest.YangMillsContinuumBridge
lake build Hardtest
```

## Import Usage

Later proof modules can reuse the pool with, for example:

```lean
import Hardtest.BlockLaplacian
import Hardtest.SigmaAxioms
import Hardtest.SigmaRegge
import Hardtest.HorizonReadout
import Hardtest.HorizonRadiationVisibility
import Hardtest.PatchVisibility
import Hardtest.GaugeTransport
import Hardtest.SourceConfluence
import Hardtest.DiscreteNoether
import Hardtest.SourceNoether
import Hardtest.YangMills
import Hardtest.YangMillsContinuumBridge
```

The canonical reusable module path for the Appendix VI admissible finite Sigma
dynamics class and joint finite Sigma axiom model is `Hardtest/SigmaAxioms.lean`.

The canonical reusable module path for the Appendix VI block-Laplacian and
spectral layer is `Hardtest/BlockLaplacian.lean`.

The canonical reusable module path for the Appendix VI sigma-Regge readout and
finite-template shape-regularity layer is `Hardtest/SigmaRegge.lean`.

The canonical reusable module path for the Appendix VI finite horizon readout
separation layer is `Hardtest/HorizonReadout.lean`.

The canonical reusable module path for the Appendix VI horizon-to-radiation
visibility criterion is `Hardtest/HorizonRadiationVisibility.lean`.

The canonical reusable module path for the finite Sigma patch visibility
threshold bridge is `Hardtest/PatchVisibility.lean`.

The canonical reusable module path for the raw atomic source-incidence
projection, finite source-confluence certificate, finite source-period carrier
registration, source-period quotient, concrete rank-three Sigma realization,
and source-admissible face-hull criterion is
`Hardtest/SourceConfluence.lean`.

The canonical reusable module path for the reduced Noether paper is
`Hardtest/DiscreteNoether.lean`.

The canonical reusable bridge from the concrete four-source confluence model
to the non-scalar cyclic reduced Noether datum is
`Hardtest/SourceNoether.lean`.

The canonical reusable module path for the Yang--Mills transport paper is
`Hardtest/YangMills.lean`.

The canonical reusable bridge module path for the conditional Yang--Mills
continuum step is `Hardtest/YangMillsContinuumBridge.lean`.
