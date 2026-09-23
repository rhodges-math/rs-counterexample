import Schubert.RS.PolynomialStringNormalization
import Schubert.RS.Sl2TwistedCompletion
import Mathlib.LinearAlgebra.StdBasis

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

/-- A concrete finite representation of highest weight d for the chosen
polynomial root algebra. Its ambient is the actual homogeneous polynomial piece. -/
abbrev polynomialIrreducible {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :=
  fullPrimitiveModule (polynomialSl2Triple a b hab) (polynomialHighestVector_primitive a b hab d)

def polynomialIrreducibleBasis {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    Module.Basis (Fin (d+1)) ℂ (polynomialIrreducible a b hab d) :=
  fullPrimitiveBasis (polynomialSl2Triple a b hab) (polynomialHighestVector_primitive a b hab d)

def polynomialIrreducibleE {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    Module.End ℂ (polynomialIrreducible a b hab d) :=
  LieModule.toEnd ℂ ((polynomialSl2Triple a b hab).toLieSubalgebra ℂ) _
    (sl2RaisingElement (polynomialSl2Triple a b hab))

def polynomialIrreducibleH {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    Module.End ℂ (polynomialIrreducible a b hab d) :=
  LieModule.toEnd ℂ ((polynomialSl2Triple a b hab).toLieSubalgebra ℂ) _
    (sl2CartanElement (polynomialSl2Triple a b hab))

theorem polynomialIrreducibleBasis_e_zero {n : ℕ} (a b : Fin n) (hab : a≠b) (d : ℕ) :
    polynomialIrreducibleE a b hab d (polynomialIrreducibleBasis a b hab d 0)=0 :=
  fullPrimitiveBasis_e_zero _ _

theorem polynomialIrreducibleBasis_e_succ {n : ℕ} (a b : Fin n) (hab : a≠b)
    (d k : ℕ) (hk : k+1<d+1) :
    polynomialIrreducibleE a b hab d (polynomialIrreducibleBasis a b hab d ⟨k+1,hk⟩)=
      ((k+1)*((d:ℂ)-k)) • polynomialIrreducibleBasis a b hab d ⟨k,by omega⟩ :=
  fullPrimitiveBasis_e_succ _ _ k hk

theorem polynomialIrreducibleBasis_h {n : ℕ} (a b : Fin n) (hab : a≠b)
    (d : ℕ) (k : Fin (d+1)) :
    polynomialIrreducibleH a b hab d (polynomialIrreducibleBasis a b hab d k)=
      ((d:ℂ)-2*k.val) • polynomialIrreducibleBasis a b hab d k :=
  fullPrimitiveBasis_h _ _ k

variable {n : ℕ} {a b : Fin n} {S : Submodule ℂ (MatrixPolynomial n)}
  (B : PolynomialRootStringBasis a b S) (hab : a≠b)

def PolynomialRootStringBasis.residual (i : B.index) : ℕ :=
  (B.weight i a-B.weight i b+(B.length i:ℤ)).toNat

include hab in
theorem PolynomialRootStringBasis.residual_cast (i : B.index) :
    (B.residual i:ℂ)=((B.weight i a-B.weight i b:ℤ):ℂ)+(B.length i:ℂ) := by
  have hn := polynomial_string_admissible a b hab (B.seed i) (B.weight i) (B.seed_weight i)
    (B.length i) (B.top_ne_zero i) (B.next_zero i)
  have hh := Int.toNat_of_nonneg hn
  change ((B.weight i a-B.weight i b+(B.length i:ℤ)).toNat:ℂ)=_
  exact_mod_cast hh

def PolynomialRootStringBasis.modelBasis :
    Module.Basis (Σ i,Fin (B.length i+1)) ℂ (∀ i,polynomialIrreducible a b hab (B.length i)) :=
  Pi.basis (fun i => polynomialIrreducibleBasis a b hab (B.length i))

def PolynomialRootStringBasis.stringEquiv :
    S ≃ₗ[ℂ] (∀ i,polynomialIrreducible a b hab (B.length i)) :=
  B.normalizedBasis.equiv (B.modelBasis hab) (Equiv.refl _)

theorem PolynomialRootStringBasis.stringEquiv_basis [DecidableEq B.index] (j : Σ i,Fin (B.length i+1)) :
    B.stringEquiv hab (B.normalizedBasis j)=
      (Pi.single j.1 (polynomialIrreducibleBasis a b hab (B.length j.1) j.2) :
        ∀ i,polynomialIrreducible a b hab (B.length i)) := by
  classical
  rw [PolynomialRootStringBasis.stringEquiv,Module.Basis.equiv_apply]
  exact Pi.basis_apply _ j

def PolynomialRootStringBasis.modelE :
    Module.End ℂ (∀ i,polynomialIrreducible a b hab (B.length i)) :=
  LinearMap.piMap (fun i => polynomialIrreducibleE a b hab (B.length i))

def PolynomialRootStringBasis.modelH :
    Module.End ℂ (∀ i,polynomialIrreducible a b hab (B.length i)) :=
  LinearMap.piMap (fun i => polynomialIrreducibleH a b hab (B.length i)+
    (B.residual i:ℂ) • LinearMap.id)

end
end Schubert.RS.Representation
