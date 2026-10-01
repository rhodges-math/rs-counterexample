import Mathlib.RepresentationTheory.Intertwining
import Mathlib.RepresentationTheory.Subrepresentation
import Mathlib.LinearAlgebra.Projection
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Spaces of intertwining maps

Elementary facts about the spaces `Hom_G(V, W)` of intertwining maps of representations over a
field, used to count multiplicities:

* intertwining maps into a product are pairs (`GLRep.intertwiningMapProdEquiv`);
* equivalences of representations induce linear equivalences of the spaces of intertwining maps
  (`GLRep.intertwiningMapCongrLeft`, `GLRep.intertwiningMapCongrRight`);
* a subrepresentation together with a complement is equivalent to the product
  (`GLRep.equivProdOfIsCompl`).

## Main results

* `GLRep.finrank_intertwiningMap_prod`: `dim Hom(V, W × W') = dim Hom(V, W) + dim Hom(V, W')`.
-/

namespace GLRep

open Module Representation

noncomputable section

variable {K G : Type*} [Field K] [Monoid G]
variable {V V' W W' : Type*} [AddCommGroup V] [Module K V] [AddCommGroup V'] [Module K V']
  [AddCommGroup W] [Module K W] [AddCommGroup W'] [Module K W']
variable {ρ : Representation K G V} {ρ' : Representation K G V'}
  {σ : Representation K G W} {τ : Representation K G W'}

/-- **Intertwining maps into a product** are pairs of intertwining maps. -/
def intertwiningMapProdEquiv :
    IntertwiningMap ρ (σ.prod τ) ≃ₗ[K] IntertwiningMap ρ σ × IntertwiningMap ρ τ where
  toFun f := ((IntertwiningMap.fst K σ τ).comp f, (IntertwiningMap.snd K σ τ).comp f)
  invFun p := p.1.prod p.2
  map_add' _ _ := Prod.ext (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
    (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  map_smul' _ _ := Prod.ext (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
    (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
  left_inv _ := IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  right_inv _ := Prod.ext (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))
    (IntertwiningMap.ext (LinearMap.ext fun _ => rfl))

/-- `dim Hom(V, W × W') = dim Hom(V, W) + dim Hom(V, W')`. -/
theorem finrank_intertwiningMap_prod [FiniteDimensional K (IntertwiningMap ρ σ)]
    [FiniteDimensional K (IntertwiningMap ρ τ)] :
    finrank K (IntertwiningMap ρ (σ.prod τ)) =
      finrank K (IntertwiningMap ρ σ) + finrank K (IntertwiningMap ρ τ) := by
  rw [intertwiningMapProdEquiv.finrank_eq, Module.finrank_prod]

/-- An equivalence of targets induces a linear equivalence of the spaces of intertwining maps. -/
def intertwiningMapCongrRight (e : σ.Equiv τ) :
    IntertwiningMap ρ σ ≃ₗ[K] IntertwiningMap ρ τ where
  toFun f := e.toIntertwiningMap.comp f
  invFun f := e.symm.toIntertwiningMap.comp f
  map_add' f g := IntertwiningMap.ext (LinearMap.ext fun v => by
    change e (f v + g v) = e (f v) + e (g v)
    exact map_add _ _ _)
  map_smul' c f := IntertwiningMap.ext (LinearMap.ext fun v => by
    change e (c • f v) = c • e (f v)
    exact map_smul _ _ _)
  left_inv f := IntertwiningMap.ext (LinearMap.ext fun v => e.symm_apply_apply (f v))
  right_inv f := IntertwiningMap.ext (LinearMap.ext fun v => e.apply_symm_apply (f v))

/-- An equivalence of sources induces a linear equivalence of the spaces of intertwining maps. -/
def intertwiningMapCongrLeft (e : ρ.Equiv ρ') :
    IntertwiningMap ρ σ ≃ₗ[K] IntertwiningMap ρ' σ where
  toFun f := f.comp e.symm.toIntertwiningMap
  invFun f := f.comp e.toIntertwiningMap
  map_add' _ _ := IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  map_smul' _ _ := IntertwiningMap.ext (LinearMap.ext fun _ => rfl)
  left_inv f := IntertwiningMap.ext (LinearMap.ext fun v => by
    change f (e.symm (e v)) = f v
    rw [e.symm_apply_apply])
  right_inv f := IntertwiningMap.ext (LinearMap.ext fun v => by
    change f (e (e.symm v)) = f v
    rw [e.apply_symm_apply])

/-- A subrepresentation is complemented in the lattice of subrepresentations exactly when its
underlying subspace is complemented by the underlying subspace. -/
theorem isCompl_toSubmodule {U U' : Subrepresentation σ} (h : IsCompl U U') :
    IsCompl U.toSubmodule U'.toSubmodule := by
  refine IsCompl.of_eq ?_ ?_
  · rw [← Subrepresentation.toSubmodule_inf, h.inf_eq_bot]
    rfl
  · rw [← Subrepresentation.toSubmodule_sup, h.sup_eq_top]
    rfl

/-- **A subrepresentation and a complement**: the representation is equivalent to their
product. -/
def equivProdOfIsCompl {U U' : Subrepresentation σ} (h : IsCompl U U') :
    (U.toRepresentation.prod U'.toRepresentation).Equiv σ :=
  .mk (Submodule.prodEquivOfIsCompl _ _ (isCompl_toSubmodule h)) fun g =>
    LinearMap.ext fun x => by
      simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe,
        Submodule.coe_prodEquivOfIsCompl', map_add]
      rfl

end

end GLRep
