import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.SMul

/-!
# Basic algebraic definitions

The free abelian group on a type, with its native `ℤ`-module structure.
-/

namespace Schubert

/-- The free abelian group with basis indexed by `α`. -/
abbrev FreeAbelian (α : Type*) := α →₀ ℤ

/-- Use the native finsupp module structure on free abelian groups.  This
specific instance prevents Lean from alternately choosing the generic
integer module structure on additive groups, which is extensionally equal
but not definitionally identical to `Finsupp.module`. -/
noncomputable abbrev freeAbelianModule (α : Type*) :
    Module ℤ (FreeAbelian α) :=
  Finsupp.module α ℤ

attribute [instance 1100] freeAbelianModule

/-- The standard basis vector of a free abelian group. -/
noncomputable def basisVector {α : Type*} (a : α) : FreeAbelian α :=
  Finsupp.single a 1

end Schubert
