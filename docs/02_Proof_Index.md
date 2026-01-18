# Proof Index

## Key Theorems

### Tropical Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `relu_is_tropical` | Tropical/ReLU.lean | ReLU(x) = max(0, x) is tropical addition with 0 |
| `relu_neuron_is_tropical` | Tropical/ReLU.lean | ReLU neuron computes tropical polynomial |
| `relu_layer_is_tropical` | Tropical/ReLU.lean | ReLU layer is tropical rational map |
| `tadd_comm` | Tropical/Semiring.lean | Tropical addition is commutative |
| `tadd_assoc` | Tropical/Semiring.lean | Tropical addition is associative |
| `tmul_distrib` | Tropical/Semiring.lean | Tropical multiplication distributes |

### Differential Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `chainRule` | Differential/Derivative.lean | Chain rule for dual numbers |
| `S_derivative_correct` | Differential/Derivative.lean | S combinator derivative via Leibniz rule |
| `dualApp_chainRule_consistent` | Differential/Derivative.lean | dualApp consistent with chainRule |
| `derivativeApp1_apply` | Differential/Derivative.lean | Derivative of application (first arg) |
| `derivativeApp2_apply` | Differential/Derivative.lean | Derivative of application (second arg) |

### Active Inference Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `freeEnergy_bounds_surprise` | ActiveInference/FreeEnergy.lean | F ≥ -log p(o) (Jensen) |
| `freeEnergy_kl_decomposition` | ActiveInference/FreeEnergy.lean | F = KL + surprise |

### Renormalization Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `deep_rg_converges` | Renormalization/CoarseGrain.lean | Deep RG flow converges to fixed point |

### Futamura Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `compile_correct` | ProgramCalculus/Futamura.lean | First Futamura projection correctness |
| `futamura_preserves_reconstruction` | ProgramCalculus/AdelicFutamura.lean | Specialization preserves reconstruction |
| `specialization_finite_lens_activity` | ProgramCalculus/AdelicFutamura.lean | Only finitely many lenses change |

### Topos/Sheaf Layer

| Theorem | File | Statement |
|---------|------|-----------|
| `sheaf_diffusion_converges` | Topos/SheafNeuralNet.lean | Sheaf diffusion → harmonic sections |
| `cohomology_alignment_obstruction` | Topos/SheafNeuralNet.lean | H¹ ≠ 0 → alignment obstruction |
| `closedSieves_isSheaf` | Topos/ClosedSievesHeyting.lean | Closed sieves form a sheaf |

### Combinators

| Theorem | File | Statement |
|---------|------|-----------|
| `I_reduces` | LoF/Combinators/SKYExec.lean | I x →* x |
| `stepEdges_sound` | LoF/Combinators/SKYMultiway.lean | Multiway reduction is sound |
| `stepEdges_complete` | LoF/Combinators/SKYMultiway.lean | All reductions are captured |

## Structures

| Structure | Module | Purpose |
|-----------|--------|---------|
| `TropicalReal` | Tropical | Extended reals for tropical semiring |
| `ReLUNeuron` | Tropical | Single ReLU neuron |
| `ReLULayer` | Tropical | Layer of ReLU neurons |
| `Dual` | Differential | Dual number (value + tangent) |
| `GenerativeModel` | ActiveInference | p(o,s) joint distribution |
| `RecognitionModel` | ActiveInference | q(s|o) approximate posterior |
| `CoarseGrain` | Renormalization | Fine → Coarse mapping |
| `RGTransform` | Renormalization | Scale transformation |
| `DeepRG` | Renormalization | Sequence of RG transforms |
| `Language` | ProgramCalculus | Program, Input, Output, eval |
| `Mix` | ProgramCalculus | Partial evaluator |
| `InterpModel` | ProgramCalculus | Interpreter model |
| `AdelicProgramOps` | ProgramCalculus | Adelic operations on programs |
| `CellularSheaf` | Topos | Sheaf on a graph |
| `SheafNNLayer` | Topos | Sheaf neural network layer |
| `LensData` | Embeddings | Multi-scale lens structure |
