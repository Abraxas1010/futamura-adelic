# Lean Module Map

## Overview

The Futamura-Adelic package implements the "Organic Alignment" mathematical stack in Lean 4.

## Module Structure

```
HeytingLean/
├── Tropical/              # Tropical geometry (ReLU = max)
│   ├── Semiring.lean      # (ℝ ∪ {-∞}, max, +) semiring
│   ├── ReLU.lean          # ReLU as tropical polynomial
│   └── Differential.lean  # Tropical-differential connection
│
├── ActiveInference/       # Free energy principle
│   ├── FreeEnergy.lean    # Variational free energy F
│   ├── Agent.lean         # Active inference agents
│   └── AdelicFreeEnergy.lean  # Multi-scale free energy
│
├── Renormalization/       # RG flow ≈ deep learning
│   ├── CoarseGrain.lean   # RG transformations
│   ├── Differential.lean  # Beta functions
│   └── Adelic.lean        # Coupled multi-scale RG
│
├── ProgramCalculus/       # Futamura projections
│   ├── Core.lean          # Language, ObsEq
│   ├── Futamura.lean      # First projection
│   ├── AdelicOps.lean     # Adelic program operations
│   ├── AdelicFutamura.lean    # Adelic-Futamura connection
│   └── AdelicOpsInstances/
│       └── SKYAdelic.lean # Non-trivial instance
│
├── LoF/Combinators/       # Laws of Form + combinators
│   ├── SKY.lean           # S, K, Y combinators
│   ├── SKYExec.lean       # Reduction engine
│   ├── SKYMultiway.lean   # Multiway graph
│   ├── Differential/      # Dual numbers, chain rule
│   │   ├── Derivative.lean
│   │   ├── LinearComb.lean
│   │   └── VectorSpace.lean
│   ├── Topos/             # Sheaves, nuclei
│   │   ├── SheafNeuralNet.lean
│   │   ├── SieveFrame.lean
│   │   ├── SieveNucleus.lean
│   │   └── ClosedSievesHeyting.lean
│   └── Heyting/
│       └── Nucleus.lean
│
├── Embeddings/
│   └── Adelic.lean        # Restricted product structure
│
├── Tests/Integration/
│   └── OrganicAlignmentStack.lean
│
└── CLI/                   # Executable demos
    ├── TropicalReLUDemoMain.lean
    ├── FreeEnergyDemoMain.lean
    ├── RGFlowDemoMain.lean
    ├── SheafDiffusionDemoMain.lean
    ├── AdelicFutamuraDemoMain.lean
    └── OrganicAlignmentStackTestMain.lean
```

## Key Dependencies

- **Mathlib v4.24.0**: Core mathematics library
- **Batteries**: Extended standard library

## Import Graph

The modules form a layered structure:

```
Tropical ──┐
           ├──> Differential ──┐
ActiveInf ─┤                   ├──> Integration
           ├──> Adelic ────────┤
RG ────────┘                   │
                               │
Futamura ──> AdelicFutamura ───┘
```
