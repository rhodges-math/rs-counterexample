import Schubert.RS.Representation.CyclicGeneration

namespace Schubert.RS.Representation
noncomputable section
attribute [local instance 100] LieRing.ofAssociativeRing

/-- Intertwining the Lie generators implies intertwining their actual
enveloping-algebra representations. No PBW theorem is used. -/
theorem enveloping_intertwines {n : ℕ} {X Y : Type*}
    [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y]
    (ρ : Enveloping n →ₐ[ℂ] Module.End ℂ X)
    (σ : Enveloping n →ₐ[ℂ] Module.End ℂ Y) (f : X →ₗ[ℂ] Y)
    (hf : ∀ A x, f (ρ (UniversalEnvelopingAlgebra.ι ℂ A) x) =
      σ (UniversalEnvelopingAlgebra.ι ℂ A) (f x))
    (a : Enveloping n) (x : X) : f (ρ a x) = σ a (f x) := by
  induction a using enveloping_induction generalizing x with
  | hC c => simp
  | hι A => exact hf A x
  | hmul a b ha hb =>
      change f ((ρ (a*b)) x) = (σ (a*b)) (f x)
      rw [map_mul,map_mul]
      exact (ha (ρ b x)).trans (congrArg (σ a) (hb x))
  | hadd a b ha hb => simp only [map_add,LinearMap.add_apply,ha,hb]

variable {n : ℕ} (S : Submodule ℂ (MatrixPolynomial n))
  (hS : ∀ r : PositiveRoot n, ∀ p∈S, matrixUnitDerivation r.val.1 r.val.2 p∈S)

/-- The original polynomial enveloping action restricted to an actual
positive-root-stable polynomial subspace. -/
def polynomialSubmoduleEnveloping : Enveloping n →ₐ[ℂ] Module.End ℂ S where
  toFun a := ((polynomialEnveloping n a).comp S.subtype).codRestrict S
    (fun p => root_stable_enveloping S hS a p.property)
  map_zero' := by apply LinearMap.ext; intro p; apply Subtype.ext; exact LinearMap.congr_fun (map_zero _) p.val
  map_one' := by apply LinearMap.ext; intro p; apply Subtype.ext; exact LinearMap.congr_fun (map_one _) p.val
  map_add' a b := by apply LinearMap.ext; intro p; apply Subtype.ext; exact LinearMap.congr_fun (map_add _ a b) p.val
  map_mul' a b := by apply LinearMap.ext; intro p; apply Subtype.ext; exact LinearMap.congr_fun (map_mul _ a b) p.val
  commutes' c := by apply LinearMap.ext; intro p; apply Subtype.ext; exact LinearMap.congr_fun ((polynomialEnveloping n).commutes c) p.val

theorem polynomialSubmoduleEnveloping_val (a : Enveloping n) (p : S) :
    (polynomialSubmoduleEnveloping S hS a p : MatrixPolynomial n) =
      polynomialEnveloping n a p.val := rfl

@[instance_reducible] def polynomialSubmoduleEnvelopingModule : Module (Enveloping n) S :=
  Module.compHom S (polynomialSubmoduleEnveloping S hS).toRingHom

end
end Schubert.RS.Representation
