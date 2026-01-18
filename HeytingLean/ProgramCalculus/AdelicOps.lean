import HeytingLean.ProgramCalculus.Core
import HeytingLean.Embeddings.Adelic

/-!
# ProgramCalculus.AdelicOps

An interface for testing “adelic arithmetic as program transformation” hypotheses.

The intent is **not** to assert identities like “multiplication *is* partial evaluation”.
Instead, we:

* define a lens-indexed depth/valuation `Depth := LensID → Int`,
* expose program operations (`mul`, `add`, `normalize`, `renormDiv`),
* require *valuation-style laws* and a *division reconstruction* law.

Concrete instantiations can then be validated both in Lean (semantic laws) and at runtime
(via the repo’s executable pipeline).
-/

namespace HeytingLean
namespace ProgramCalculus

open HeytingLean.Embeddings

/-- Lens-indexed “depth/valuation” (adelic-style). -/
abbrev Depth : Type :=
  LensID → Int

/-- Abstract operations and laws making the “adelic arithmetic” hypothesis testable. -/
structure AdelicProgramOps (language : Language) where
  depth : language.Program → Depth
  mul : language.Program → language.Program → language.Program
  add : language.Program → language.Program → language.Program
  normalize : language.Program → language.Program
  renormDiv : language.Program → language.Program → language.Program × language.Program

  /- ### Laws (the “why”) -/

  /-- Multiplicative depth law (valuation additivity). -/
  depth_mul :
    ∀ (a b : language.Program) (lens : LensID),
      depth (mul a b) lens = depth a lens + depth b lens

  /-- Additive depth law (valuation inequality; adelic/p-adic style). -/
  depth_add :
    ∀ (a b : language.Program) (lens : LensID),
      min (depth a lens) (depth b lens) ≤ depth (add a b) lens

  /-- Normalization does not increase depth. -/
  depth_norm :
    ∀ (a : language.Program) (lens : LensID),
      depth (normalize a) lens ≤ depth a lens

  /-- Division-style reconstruction: quotient+residual recombine back to the original, semantically. -/
  div_reconstruct :
    ∀ (a e : language.Program),
      let (q, r) := renormDiv a e
      ObsEq language (add (mul q e) r) a

end ProgramCalculus
end HeytingLean
