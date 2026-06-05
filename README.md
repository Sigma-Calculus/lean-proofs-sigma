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

- `Hardtest.GaugeTransport`
  - File: `Hardtest/GaugeTransport.lean`
  - Source paper context: gauge-like transport, local exactness, cube/Bianchi core,
    finite plaquette algebra, and reduced holonomy Noether core.

- `Hardtest.DiscreteNoether`
  - File: `Hardtest/DiscreteNoether.lean`
  - Source paper context: finite reduced-holonomy Noether charge,
    model-independent cyclic conservation, and functorial isometric transport.

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
lake build Hardtest.GaugeTransport
lake build Hardtest.DiscreteNoether
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
import Hardtest.GaugeTransport
import Hardtest.DiscreteNoether
import Hardtest.YangMills
import Hardtest.YangMillsContinuumBridge
```

The canonical reusable module path for the Appendix VI admissible finite Sigma
dynamics class and joint finite Sigma axiom model is `Hardtest/SigmaAxioms.lean`.
The canonical reusable module path for the Appendix VI block-Laplacian and
spectral layer is `Hardtest/BlockLaplacian.lean`.
The canonical reusable module path for the Appendix VI sigma-Regge readout and
finite-template shape-regularity layer is `Hardtest/SigmaRegge.lean`.
The canonical reusable module path for the reduced Noether paper is
`Hardtest/DiscreteNoether.lean`.
The canonical reusable module path for the Yang--Mills transport paper is
`Hardtest/YangMills.lean`.
The canonical reusable bridge module path for the conditional Yang--Mills
continuum step is `Hardtest/YangMillsContinuumBridge.lean`.
