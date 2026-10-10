import RSCounterexample.Paper.Quiver.LeviShape
import RSCounterexample.Paper.HighestWeight.Integration
import TauCeti.RepresentationTheory.ClassicalGroups.DominantWeight
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic
import TauCeti.RepresentationTheory.LinearCharacter
import Mathlib.RepresentationTheory.Intertwining
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.LinearAlgebra.Trace
import Mathlib.Combinatorics.Enumerative.Composition

/-!
# Representations of a standard Levi subgroup

The group `L = GL_{d_0}(ℂ) × ⋯ × GL_{d_{s−1}}(ℂ)` of Theorem 5.3 of the paper, and the genuine
representation-theoretic objects its statement mentions:

* polynomial representations of `L` and their characters (traces on the diagonal torus);
* the irreducible representations `⊗_p V_p^{λ^{(p)}}`. Each `V_p^{μ}` with `μ` a partition is the
  flag-minor span `flagOrbitSpan` of the highest flag polynomial, the irreducible representation
  of `GL_{d_p}(ℂ)` with highest weight `μ` (`Schubert.RS.HighestWeight`). Weights with negative
  entries are reached by twisting with powers of the determinants.

## Main definitions

* `Schubert.RS.GL.LeviGroup`: the group `L`.
* `Schubert.RS.GL.IntervalLevi`: the group `L_I` of an interval partition `I` of `n`.
* `Schubert.RS.GL.leviTorus`: the diagonal torus element with given entries.
* `Schubert.RS.GL.IsPolynomialLeviRep`: a representation of `L` whose matrix entries are polynomials
  in the matrix entries of the factors.
* `Schubert.RS.GL.IsLeviCharacter`: a polynomial is the character of a representation.
* `Schubert.RS.GL.extTensor`: the external tensor product of representations of the factors.
* `Schubert.RS.GL.leviDetChar`, `leviTwist`: the character `∏_p det(g_p)^{k_p}` and twisting by it.
* `Schubert.RS.GL.polyShape`: the column multiplicities of `λ − λ_last` for a dominant weight `λ`.
* `Schubert.RS.GL.leviIrrep`: `⊗_p V_p^{μ_p}` for partitions `μ_p` given by column multiplicities.
* `Schubert.RS.GL.ratLeviIrrep`: `⊗_p V_p^{λ^{(p)}}` for dominant integer weights `λ^{(p)}`.
-/

namespace Schubert.RS.GL

noncomputable section

open Matrix Schubert.RS.Representation Schubert.RS.HighestWeight

variable {s : ℕ} (d : Fin s → ℕ)

/-- The standard Levi subgroup `L = GL_{d_0}(ℂ) × ⋯ × GL_{d_{s−1}}(ℂ)`. -/
abbrev LeviGroup : Type := (p : Fin s) → GL (Fin (d p)) ℂ

/-- The standard Levi subgroup `L_I = ∏_p GL_{|I_p|}(ℂ)` of an interval partition `I` of `n`,
given as a composition of `n`. -/
abbrev IntervalLevi {n : ℕ} (I : _root_.Composition n) : Type := LeviGroup I.blocksFun

theorem total_blocksFun {n : ℕ} (I : _root_.Composition n) : Quiver.Levi.total I.blocksFun = n :=
  I.sum_blocksFun

/-- The element `diag(t)` of the diagonal torus of `L`, block by block. -/
def leviTorus (t : Fin (Quiver.Levi.total d) → ℂˣ) : LeviGroup d :=
  fun p => TauCeti.diagGL fun i => t (Quiver.Levi.pos d p i)

/-- A representation of `L` is **polynomial** when, in some basis, every matrix entry of `ρ g` is a
polynomial in the entries of the matrices `g_p`. -/
def IsPolynomialLeviRep {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : _root_.Representation ℂ (LeviGroup d) W) : Prop :=
  ∃ (b : Module.Basis (Fin (Module.finrank ℂ W)) ℂ W)
    (P : Fin (Module.finrank ℂ W) → Fin (Module.finrank ℂ W) →
      MvPolynomial (Σ p : Fin s, Fin (d p) × Fin (d p)) ℂ),
    ∀ (g : LeviGroup d) (i j : Fin (Module.finrank ℂ W)),
      LinearMap.toMatrix b b (ρ g) i j =
        MvPolynomial.eval (fun x => (g x.1 : Matrix (Fin (d x.1)) (Fin (d x.1)) ℂ) x.2.1 x.2.2)
          (P i j)

/-- `χ` is the **character** of `ρ`: at every element `diag(t)` of the diagonal torus, the trace of
`ρ(diag t)` is `χ(t)`. -/
def IsLeviCharacter {W : Type*} [AddCommGroup W] [Module ℂ W]
    (ρ : _root_.Representation ℂ (LeviGroup d) W)
    (χ : Schubert.RS.Polynomial (Quiver.Levi.total d)) : Prop :=
  ∀ t : Fin (Quiver.Levi.total d) → ℂˣ,
    LinearMap.trace ℂ W (ρ (leviTorus d t)) =
      MvPolynomial.eval₂ (Int.castRingHom ℂ) (fun i => (t i : ℂ)) χ

/-- The **external tensor product** `⊗_p W_p` of representations `W_p` of the factors
`GL_{d_p}(ℂ)`: `g` acts by `⊗_p ρ_p(g_p)`. -/
def extTensor {W : Fin s → Type*} [∀ p, AddCommMonoid (W p)] [∀ p, Module ℂ (W p)]
    (ρ : (p : Fin s) → _root_.Representation ℂ (GL (Fin (d p)) ℂ) (W p)) :
    _root_.Representation ℂ (LeviGroup d) (PiTensorProduct ℂ W) :=
  PiTensorProduct.mapMonoidHom.comp
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => GL (Fin (d p)) ℂ) p))

/-- The character `g ↦ ∏_p det(g_p)^{k_p}` of `L`. -/
def leviDetCharacter (k : Fin s → ℤ) : LeviGroup d →* ℂˣ :=
  ∏ p, ((Matrix.GeneralLinearGroup.det : GL (Fin (d p)) ℂ →* ℂˣ) ^ (k p)).comp
    (Pi.evalMonoidHom (fun p => GL (Fin (d p)) ℂ) p)

/-- The one-dimensional representation of `L` with character `∏_p det(g_p)^{k_p}`. -/
def leviDetChar (k : Fin s → ℤ) : _root_.Representation ℂ (LeviGroup d) ℂ :=
  _root_.Representation.ofLinearCharacter (leviDetCharacter d k)

/-- The twist `W ⊗ ∏_p det_p^{k_p}` of a representation of `L`. -/
def leviTwist {W : Type*} [AddCommMonoid W] [Module ℂ W]
    (ρ : _root_.Representation ℂ (LeviGroup d) W) (k : Fin s → ℤ) :
    _root_.Representation ℂ (LeviGroup d) (TensorProduct ℂ W ℂ) :=
  ρ.tprod (leviDetChar d k)

/-- The column multiplicities of the partition `λ − λ_last`, for a dominant weight `λ` of `GL_m`:
the shape of the flag-minor model of the polynomial part of `λ`. -/
def polyShape {m : ℕ} (lam : TauCeti.DominantWeight m) : ColumnShape m :=
  columnsOfWeight fun i => (lam.1 i - lam.detShift).toNat

theorem shapeWeight_polyShape {m : ℕ} (lam : TauCeti.DominantWeight m) :
    shapeWeight (polyShape lam) = fun i => (lam.1 i - lam.detShift).toNat :=
  shapeWeight_columnsOfWeight _ fun _ _ hij => Int.toNat_le_toNat (by
    have := lam.antitone hij
    omega)

/-- `⊗_p V_p^{μ_p}` for partitions `μ_p` given by their column multiplicities: the external tensor
product of the flag-minor models `flagOrbitRepresentation (μ p)`, each the irreducible
representation of `GL_{d_p}(ℂ)` with highest weight `shapeWeight (μ p)`
(`flagOrbitRepresentation_isIrreducible`, `nonempty_equiv_flagOrbitRepresentation`). -/
def leviIrrep (μ : (p : Fin s) → ColumnShape (d p)) :
    _root_.Representation ℂ (LeviGroup d) (PiTensorProduct ℂ fun p => flagOrbitSpan (μ p)) :=
  extTensor d fun p => flagOrbitRepresentation (μ p)

/-- **The irreducible representation `⊗_p V_p^{λ^{(p)}}`** of `L` for dominant integer weights
`λ^{(p)}`: the flag-minor models of the partitions `λ^{(p)} − λ^{(p)}_{last}`, twisted by
`∏_p det(g_p)^{λ^{(p)}_{last}}`. -/
def ratLeviIrrep (lam : (p : Fin s) → TauCeti.DominantWeight (d p)) :
    _root_.Representation ℂ (LeviGroup d)
      (TensorProduct ℂ (PiTensorProduct ℂ fun p => flagOrbitSpan (polyShape (lam p))) ℂ) :=
  leviTwist d (leviIrrep d fun p => polyShape (lam p)) fun p => (lam p).detShift

end

end Schubert.RS.GL
