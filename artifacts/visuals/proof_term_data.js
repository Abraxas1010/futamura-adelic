// Proof Term DAG Data for Futamura-Adelic Key Theorems
// Shows the structure of proof terms (applications, abstractions, etc.)

const proofTermData = {
  theorems: [
    {
      id: "compile_correct",
      name: "compile_correct",
      file: "ProgramCalculus/Futamura.lean",
      description: "First Futamura projection correctness",
      termStructure: "Eq.trans (mix.correct ...) (model.correct ...)",
      nodes: [
        { id: "root", type: "app", label: "Eq.trans", depth: 0 },
        { id: "h1", type: "app", label: "mix.correct", depth: 1 },
        { id: "h2", type: "app", label: "model.correct", depth: 1 },
        { id: "h1_prog", type: "const", label: "model.interp", depth: 2 },
        { id: "h1_stat", type: "var", label: "code", depth: 2 },
        { id: "h1_dyn", type: "var", label: "input", depth: 2 },
        { id: "h2_code", type: "var", label: "code", depth: 2 },
        { id: "h2_inp", type: "var", label: "input", depth: 2 }
      ],
      edges: [
        { from: "root", to: "h1" },
        { from: "root", to: "h2" },
        { from: "h1", to: "h1_prog" },
        { from: "h1", to: "h1_stat" },
        { from: "h1", to: "h1_dyn" },
        { from: "h2", to: "h2_code" },
        { from: "h2", to: "h2_inp" }
      ]
    },
    {
      id: "chainRule",
      name: "chainRule",
      file: "LoF/Combinators/Differential/Derivative.lean",
      description: "Chain rule for differentiable composition",
      termStructure: "fun x dx => calc ... = ... = ... = ...",
      nodes: [
        { id: "root", type: "lam", label: "λ x dx", depth: 0 },
        { id: "calc", type: "calc", label: "calc", depth: 1 },
        { id: "step1", type: "eq", label: "(f ∘ g)(x+dx) = f(g(x+dx))", depth: 2 },
        { id: "step2", type: "eq", label: "= f(g x + Dg dx)", depth: 2 },
        { id: "step3", type: "eq", label: "= f(g x) + Df(Dg dx)", depth: 2 },
        { id: "step4", type: "eq", label: "= (f∘g) x + (Df∘Dg) dx", depth: 2 },
        { id: "rfl1", type: "const", label: "rfl", depth: 3 },
        { id: "simp_hg", type: "app", label: "simp [hg']", depth: 3 },
        { id: "simpa_hf", type: "app", label: "simpa using hf", depth: 3 },
        { id: "simp_comp", type: "app", label: "simp [comp_apply]", depth: 3 }
      ],
      edges: [
        { from: "root", to: "calc" },
        { from: "calc", to: "step1" },
        { from: "calc", to: "step2" },
        { from: "calc", to: "step3" },
        { from: "calc", to: "step4" },
        { from: "step1", to: "rfl1" },
        { from: "step2", to: "simp_hg" },
        { from: "step3", to: "simpa_hf" },
        { from: "step4", to: "simp_comp" }
      ]
    },
    {
      id: "S_derivative_correct",
      name: "S_derivative_correct",
      file: "LoF/Combinators/Differential/Derivative.lean",
      description: "S combinator differentiation",
      termStructure: "simp ... : dualApp (dualApp ...) (dualApp ...) = ⟨base, tangent⟩",
      nodes: [
        { id: "root", type: "app", label: "simp_lemma", depth: 0 },
        { id: "goal", type: "eq", label: "dualApp(...) = ⟨S_denote, S_derivative⟩", depth: 1 },
        { id: "lhs", type: "app", label: "dualApp", depth: 2 },
        { id: "rhs", type: "mk", label: "⟨base, tangent⟩", depth: 2 },
        { id: "da1", type: "app", label: "dualApp ⟨x,dx⟩ ⟨z,dz⟩", depth: 3 },
        { id: "da2", type: "app", label: "dualApp ⟨y,dy⟩ ⟨z,dz⟩", depth: 3 },
        { id: "base", type: "app", label: "S_denote x y z", depth: 3 },
        { id: "tang", type: "app", label: "S_derivative (dx,dy,dz)", depth: 3 },
        { id: "simp1", type: "const", label: "S_denote", depth: 4 },
        { id: "simp2", type: "const", label: "dualApp", depth: 4 },
        { id: "simp3", type: "const", label: "app_add_left", depth: 4 },
        { id: "simp4", type: "const", label: "app_add_right", depth: 4 },
        { id: "simp5", type: "const", label: "add_assoc", depth: 4 }
      ],
      edges: [
        { from: "root", to: "goal" },
        { from: "goal", to: "lhs" },
        { from: "goal", to: "rhs" },
        { from: "lhs", to: "da1" },
        { from: "lhs", to: "da2" },
        { from: "rhs", to: "base" },
        { from: "rhs", to: "tang" },
        { from: "root", to: "simp1" },
        { from: "root", to: "simp2" },
        { from: "root", to: "simp3" },
        { from: "root", to: "simp4" },
        { from: "root", to: "simp5" }
      ]
    },
    {
      id: "relu_is_tropical",
      name: "relu_is_tropical",
      file: "Tropical/ReLU.lean",
      description: "ReLU equals tropical max-plus",
      termStructure: "simp [relu, toReal] : max 0 x = max 0 x",
      nodes: [
        { id: "root", type: "app", label: "Eq.refl", depth: 0 },
        { id: "term", type: "app", label: "max 0 x", depth: 1 },
        { id: "max", type: "const", label: "max", depth: 2 },
        { id: "zero", type: "const", label: "0", depth: 2 },
        { id: "x", type: "var", label: "x", depth: 2 },
        { id: "unfold1", type: "unfold", label: "unfold relu", depth: 3 },
        { id: "unfold2", type: "unfold", label: "unfold toReal", depth: 3 }
      ],
      edges: [
        { from: "root", to: "term" },
        { from: "term", to: "max" },
        { from: "term", to: "zero" },
        { from: "term", to: "x" },
        { from: "max", to: "unfold1" },
        { from: "max", to: "unfold2" }
      ]
    },
    {
      id: "relu_neuron_is_tropical",
      name: "relu_neuron_is_tropical",
      file: "Tropical/ReLU.lean",
      description: "ReLU neuron as tropical polynomial",
      termStructure: "⟨witness, fun input => simp ...⟩",
      nodes: [
        { id: "root", type: "mk", label: "⟨_, _⟩", depth: 0 },
        { id: "witness", type: "mk", label: "TropicalPolynomial.mk", depth: 1 },
        { id: "proof", type: "lam", label: "λ input", depth: 1 },
        { id: "terms", type: "list", label: "[zero_affine, neuron_affine]", depth: 2 },
        { id: "simp", type: "app", label: "simp", depth: 2 },
        { id: "t1", type: "mk", label: "{w:=0, b:=0}", depth: 3 },
        { id: "t2", type: "mk", label: "{w:=neuron.w, b:=neuron.b}", depth: 3 },
        { id: "s1", type: "const", label: "ReLUNeuron.eval", depth: 3 },
        { id: "s2", type: "const", label: "TropicalPolynomial.eval", depth: 3 },
        { id: "s3", type: "const", label: "relu", depth: 3 }
      ],
      edges: [
        { from: "root", to: "witness" },
        { from: "root", to: "proof" },
        { from: "witness", to: "terms" },
        { from: "proof", to: "simp" },
        { from: "terms", to: "t1" },
        { from: "terms", to: "t2" },
        { from: "simp", to: "s1" },
        { from: "simp", to: "s2" },
        { from: "simp", to: "s3" }
      ]
    },
    {
      id: "futamura_preserves_reconstruction",
      name: "futamura_preserves_reconstruction",
      file: "ProgramCalculus/AdelicFutamura.lean",
      description: "Specialization preserves reconstruction",
      termStructure: "compile_correct mix model code input",
      nodes: [
        { id: "root", type: "app", label: "compile_correct", depth: 0 },
        { id: "mix", type: "var", label: "mix", depth: 1 },
        { id: "model", type: "var", label: "model", depth: 1 },
        { id: "code", type: "var", label: "code", depth: 1 },
        { id: "input", type: "var", label: "input", depth: 1 },
        { id: "ref", type: "const", label: "← compile_correct", depth: 2 }
      ],
      edges: [
        { from: "root", to: "mix" },
        { from: "root", to: "model" },
        { from: "root", to: "code" },
        { from: "root", to: "input" },
        { from: "root", to: "ref" }
      ]
    }
  ],

  nodeColors: {
    app: "#3b82f6",      // blue - application
    lam: "#8b5cf6",      // purple - lambda
    var: "#22c55e",      // green - variable
    const: "#f59e0b",    // amber - constant
    eq: "#06b6d4",       // cyan - equality
    mk: "#ec4899",       // pink - constructor
    calc: "#14b8a6",     // teal - calc block
    list: "#f97316",     // orange - list
    unfold: "#64748b"    // slate - unfold step
  },

  nodeShapes: {
    app: "rect",
    lam: "diamond",
    var: "ellipse",
    const: "rect",
    eq: "hexagon",
    mk: "rect",
    calc: "rect",
    list: "rect",
    unfold: "rect"
  }
};

if (typeof module !== 'undefined') module.exports = proofTermData;
