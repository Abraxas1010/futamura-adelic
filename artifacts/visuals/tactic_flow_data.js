// Tactic Flow Graph Data for Futamura-Adelic Key Theorems
// Shows the sequence of proof states and tactics

const tacticFlowData = {
  theorems: [
    {
      id: "compile_correct",
      name: "compile_correct",
      file: "ProgramCalculus/Futamura.lean",
      description: "First Futamura projection: specialized interpreter matches code semantics",
      statement: "mix.evalResidual (compile mix model code) input = model.codeSem code input",
      nodes: [
        { id: "g0", type: "goal", label: "⊢ mix.evalResidual (compile mix model code) input = model.codeSem code input", depth: 0 },
        { id: "t1", type: "tactic", label: "have h1 := mix.correct ...", depth: 1 },
        { id: "g1", type: "hypothesis", label: "h1 : mix.evalResidual (mix.apply model.interp code) input = language.eval model.interp (split.pack code input)", depth: 1 },
        { id: "t2", type: "tactic", label: "have h2 := model.correct ...", depth: 2 },
        { id: "g2", type: "hypothesis", label: "h2 : language.eval model.interp (split.pack code input) = model.codeSem code input", depth: 2 },
        { id: "t3", type: "tactic", label: "exact (h1.trans h2)", depth: 3 },
        { id: "qed", type: "qed", label: "∎", depth: 4 }
      ],
      edges: [
        { from: "g0", to: "t1", label: "" },
        { from: "t1", to: "g1", label: "introduces" },
        { from: "g1", to: "t2", label: "" },
        { from: "t2", to: "g2", label: "introduces" },
        { from: "g2", to: "t3", label: "" },
        { from: "t3", to: "qed", label: "closes" }
      ]
    },
    {
      id: "chainRule",
      name: "chainRule",
      file: "LoF/Combinators/Differential/Derivative.lean",
      description: "Chain rule for composition of differentiable functions",
      statement: "(f ∘ g) (x + dx) = (f ∘ g) x + (Df.comp Dg) dx",
      nodes: [
        { id: "g0", type: "goal", label: "⊢ ∀ x dx, (f ∘ g) (x + dx) = (f ∘ g) x + (Df.comp Dg) dx", depth: 0 },
        { id: "t1", type: "tactic", label: "intro x dx", depth: 1 },
        { id: "g1", type: "goal", label: "⊢ (f ∘ g) (x + dx) = (f ∘ g) x + (Df.comp Dg) dx", depth: 1 },
        { id: "t2", type: "tactic", label: "have hg' : g (x + dx) = g x + Dg dx := hg x dx", depth: 2 },
        { id: "g2", type: "hypothesis", label: "hg' : g (x + dx) = g x + Dg dx", depth: 2 },
        { id: "t3", type: "tactic", label: "calc", depth: 3 },
        { id: "c1", type: "calc_step", label: "(f ∘ g) (x + dx) = f (g (x + dx))", depth: 4 },
        { id: "c2", type: "calc_step", label: "_ = f (g x + Dg dx)  [by simp [hg']]", depth: 4 },
        { id: "c3", type: "calc_step", label: "_ = f (g x) + Df (Dg dx)  [by simpa using hf]", depth: 4 },
        { id: "c4", type: "calc_step", label: "_ = (f ∘ g) x + (Df.comp Dg) dx  [by simp]", depth: 4 },
        { id: "qed", type: "qed", label: "∎", depth: 5 }
      ],
      edges: [
        { from: "g0", to: "t1", label: "" },
        { from: "t1", to: "g1", label: "specializes" },
        { from: "g1", to: "t2", label: "" },
        { from: "t2", to: "g2", label: "introduces" },
        { from: "g2", to: "t3", label: "" },
        { from: "t3", to: "c1", label: "" },
        { from: "c1", to: "c2", label: "=" },
        { from: "c2", to: "c3", label: "=" },
        { from: "c3", to: "c4", label: "=" },
        { from: "c4", to: "qed", label: "closes" }
      ]
    },
    {
      id: "S_derivative_correct",
      name: "S_derivative_correct",
      file: "LoF/Combinators/Differential/Derivative.lean",
      description: "S combinator derivative via dual numbers matches Leibniz expansion",
      statement: "dualApp (dualApp ⟨x, dx⟩ ⟨z, dz⟩) (dualApp ⟨y, dy⟩ ⟨z, dz⟩) = ⟨base, tangent⟩",
      nodes: [
        { id: "g0", type: "goal", label: "⊢ dualApp (dualApp ⟨x,dx⟩ ⟨z,dz⟩) (dualApp ⟨y,dy⟩ ⟨z,dz⟩) = ⟨S_denote x y z, (S_derivative x y z) (dx,(dy,dz))⟩", depth: 0 },
        { id: "t1", type: "tactic", label: "simp [S_denote, dualApp, S_derivative_apply, ...]", depth: 1 },
        { id: "g1", type: "simp_trace", label: "unfold S_denote → FormalSum.app (FormalSum.app x z) (FormalSum.app y z)", depth: 2 },
        { id: "g2", type: "simp_trace", label: "unfold dualApp → base + tangent components", depth: 2 },
        { id: "g3", type: "simp_trace", label: "apply app_add_left, app_add_right lemmas", depth: 2 },
        { id: "g4", type: "simp_trace", label: "normalize with add_assoc, add_left_comm, add_comm", depth: 2 },
        { id: "qed", type: "qed", label: "∎", depth: 3 }
      ],
      edges: [
        { from: "g0", to: "t1", label: "" },
        { from: "t1", to: "g1", label: "" },
        { from: "t1", to: "g2", label: "" },
        { from: "t1", to: "g3", label: "" },
        { from: "t1", to: "g4", label: "" },
        { from: "g1", to: "qed", label: "" },
        { from: "g2", to: "qed", label: "" },
        { from: "g3", to: "qed", label: "" },
        { from: "g4", to: "qed", label: "closes" }
      ]
    },
    {
      id: "relu_is_tropical",
      name: "relu_is_tropical",
      file: "Tropical/ReLU.lean",
      description: "ReLU is tropical addition with 0",
      statement: "relu x = TropicalReal.toReal (TropicalReal.finite 0 + TropicalReal.finite x)",
      nodes: [
        { id: "g0", type: "goal", label: "⊢ relu x = TropicalReal.toReal (finite 0 + finite x)", depth: 0 },
        { id: "t1", type: "tactic", label: "simp [relu, TropicalReal.toReal]", depth: 1 },
        { id: "g1", type: "simp_trace", label: "unfold relu → max 0 x", depth: 2 },
        { id: "g2", type: "simp_trace", label: "unfold toReal (finite 0 + finite x) → max 0 x", depth: 2 },
        { id: "qed", type: "qed", label: "∎  (refl)", depth: 3 }
      ],
      edges: [
        { from: "g0", to: "t1", label: "" },
        { from: "t1", to: "g1", label: "" },
        { from: "t1", to: "g2", label: "" },
        { from: "g1", to: "qed", label: "" },
        { from: "g2", to: "qed", label: "closes" }
      ]
    },
    {
      id: "relu_neuron_is_tropical",
      name: "relu_neuron_is_tropical",
      file: "Tropical/ReLU.lean",
      description: "A ReLU neuron is representable as a tropical polynomial",
      statement: "∃ tp : TropicalPolynomial n, ∀ input, neuron.eval input = tp.eval input",
      nodes: [
        { id: "g0", type: "goal", label: "⊢ ∃ tp, ∀ input, neuron.eval input = tp.eval input", depth: 0 },
        { id: "t1", type: "tactic", label: "classical", depth: 1 },
        { id: "g1", type: "goal", label: "⊢ ∃ tp, ∀ input, neuron.eval input = tp.eval input  [+ Classical.dec]", depth: 1 },
        { id: "t2", type: "tactic", label: "refine ⟨⟨[zero_affine, neuron_affine]⟩, ?_⟩", depth: 2 },
        { id: "g2", type: "goal", label: "⊢ ∀ input, neuron.eval input = [0, affine].foldl max 0", depth: 2 },
        { id: "t3", type: "tactic", label: "intro input", depth: 3 },
        { id: "g3", type: "goal", label: "⊢ neuron.eval input = tp.eval input", depth: 3 },
        { id: "t4", type: "tactic", label: "simp [ReLUNeuron.eval, TropicalPolynomial.eval, relu]", depth: 4 },
        { id: "qed", type: "qed", label: "∎", depth: 5 }
      ],
      edges: [
        { from: "g0", to: "t1", label: "" },
        { from: "t1", to: "g1", label: "enables decidability" },
        { from: "g1", to: "t2", label: "" },
        { from: "t2", to: "g2", label: "provides witness" },
        { from: "g2", to: "t3", label: "" },
        { from: "t3", to: "g3", label: "specializes" },
        { from: "g3", to: "t4", label: "" },
        { from: "t4", to: "qed", label: "closes" }
      ]
    }
  ],

  nodeColors: {
    goal: "#3b82f6",        // blue
    hypothesis: "#22c55e",  // green
    tactic: "#f59e0b",      // amber
    simp_trace: "#8b5cf6",  // purple
    calc_step: "#06b6d4",   // cyan
    qed: "#10b981"          // emerald
  }
};

if (typeof module !== 'undefined') module.exports = tacticFlowData;
