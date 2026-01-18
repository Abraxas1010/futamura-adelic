import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Mathlib.Order.Filter.Cofinite

/-!
# Embeddings.Adelic

An “adelic-like” multi-lens carrier for proofs/programs.

Key design choice: reuse Mathlib’s `RestrictedProduct` with the **cofinite** filter:
an element is a dependent function `∀ ℓ, Completion ℓ` together with the property that
“for all but finitely many lenses ℓ, the component is integral/canonical”.

This matches the classical adele definition pattern and avoids reimplementing the
restricted-product infrastructure.
-/

namespace HeytingLean
namespace Embeddings

/-- Lens identifiers aligned with the repo’s existing exported “views”. -/
inductive LensID where
  | omega
  | region
  | graph
  | clifford
deriving DecidableEq, Repr

/-- Per-lens completion/canonical-subset data, plus a truncation operator. -/
structure LensData where
  Completion : LensID → Type
  Integral : ∀ lens, Set (Completion lens)
  truncate : ∀ lens, Nat → Completion lens → Completion lens

open scoped RestrictedProduct

/-- The adelic carrier: restricted product over lenses with respect to the cofinite filter. -/
abbrev AdelicRep (data : LensData) : Type _ :=
  RestrictedProduct (R := data.Completion) (A := data.Integral) Filter.cofinite

/-- A per-lens precision assignment (finite precision). -/
abbrev Precision : Type :=
  LensID → Nat

/-- Truncation-based approximation: two adelic elements agree up to the chosen per-lens precisions. -/
def Approx (data : LensData) (prec : Precision) (x y : AdelicRep data) : Prop :=
  ∀ lens,
    data.truncate lens (prec lens) (x.1 lens) =
      data.truncate lens (prec lens) (y.1 lens)

/-! ## A finite-support constructor (computationally friendly) -/

/-- A finitely-supported adelic element: only finitely many lenses may be non-integral. -/
structure FinSupport (data : LensData) where
  support : Finset LensID
  value : ∀ lens, data.Completion lens
  integral_outside : ∀ lens, lens ∉ support → value lens ∈ data.Integral lens

namespace FinSupport

/-- Convert a finitely-supported value into the Mathlib `RestrictedProduct` carrier. -/
def toAdelic {data : LensData} (fs : FinSupport data) : AdelicRep data :=
  ⟨fs.value, by
    -- `∀ᶠ lens in cofinite, fs.value lens ∈ Integral lens` ⇔ finitely many exceptions.
    refine (Filter.eventually_cofinite.2 ?_)
    refine fs.support.finite_toSet.subset ?_
    intro lens hNotIntegral
    by_cases hMem : lens ∈ fs.support
    · exact hMem
    · exfalso
      exact hNotIntegral (fs.integral_outside lens hMem)⟩

end FinSupport

end Embeddings
end HeytingLean
