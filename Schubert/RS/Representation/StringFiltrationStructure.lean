import Schubert.RS.Representation.StringFiltration

namespace Schubert.RS.Representation
noncomputable section
open FinPermutation Schubert

/-- In the low-to-high divided-power convention, E sends e_k to e_(k+1). -/
def stringRaising (d : ℕ) (z : Fin (d+1) → ℂ) (j : Fin (d+1)) : ℂ :=
  if h : j.val = 0 then 0 else z ⟨j.val-1, by omega⟩

/-- F sends e_k to k(d-k+1)e_(k-1). -/
def stringLowering (d : ℕ) (z : Fin (d+1) → ℂ) (j : Fin (d+1)) : ℂ :=
  if h : j.val+1 < d+1 then ((j.val+1)*(d-j.val) : ℕ) • z ⟨j.val+1,h⟩ else 0

def selectedStringIndex (d : ℕ) (full : Bool) :
    Fin (if full then d+1 else 1) → Fin (d+1) :=
  match full with
  | true => id
  | false => fun _ => Fin.last d

/-- A filtration whose subquotients are sl2 strings with fixed E/F
coefficients. The smaller module meets each factor in either its highest line
or the entire string; spectral exactness records the weight-space maps. -/
structure RankOneStringFiltration {n : ℕ} {M N : Type*}
    [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N]
    (σ : DiagonalTorus n →* Module.End ℂ M)
    (ρ : DiagonalTorus n →* Module.End ℂ N) (i : AdjacentPosition n) (L : ℕ)
    (embed : M →ₗ[ℂ] N) (raising lowering : Module.End ℂ N)
    extends StringSpectralFiltration σ ρ i L where
  embed_injective : Function.Injective embed
  embed_equivariant : ∀ t x, embed (σ t x) = ρ t (embed x)
  intersection : ∀ k, source.stage k = (target.stage k).comap embed
  raising_stable : ∀ k x, x ∈ target.stage k → raising x ∈ target.stage k
  lowering_stable : ∀ k x, x ∈ target.stage k → lowering x ∈ target.stage k
  coordinates : ∀ k : Fin L, target.stage (k.val+1) →ₗ[ℂ]
    (Fin (endpoint k i.left - endpoint k i.right + 1) → ℂ)
  coordinates_surjective : ∀ k, Function.Surjective (coordinates k)
  coordinates_kernel : ∀ k, LinearMap.ker (coordinates k) =
    LinearMap.range (Submodule.inclusion (target.increasing k.val))
  coordinates_torus : ∀ k t (x : target.stage (k.val+1)) j,
    coordinates k ⟨ρ t x, target.stable _ t x x.property⟩ j =
      integerWeightScalar (exponentWeight (stringWeight i (endpoint k) j)) t *
        coordinates k x j
  coordinates_raising : ∀ k (x : target.stage (k.val+1)),
    coordinates k ⟨raising x, raising_stable _ x x.property⟩ =
      stringRaising (endpoint k i.left - endpoint k i.right) (coordinates k x)
  coordinates_lowering : ∀ k (x : target.stage (k.val+1)),
    coordinates k ⟨lowering x, lowering_stable _ x x.property⟩ =
      stringLowering (endpoint k i.left - endpoint k i.right) (coordinates k x)
  source_factor_image : ∀ k z,
    (∃ x : target.stage (k.val+1), (∃ y, embed y = x.val) ∧ coordinates k x = z) ↔
      (full k = true ∨ ∀ j, j ≠ Fin.last (endpoint k i.left - endpoint k i.right) → z j = 0)
  spectral_coordinates : ∀ k w (x : ↥(target.stage (k.val+1) ⊓ torusWeightSpace ρ w))
      (j : {j // exponentWeight (stringWeight i (endpoint k) j) = w}),
    target.factor k w x j = coordinates k ⟨x.val, x.property.1⟩ j.val

  source_spectral_coordinates : ∀ k w
      (x : ↥(source.stage (k.val+1) ⊓ torusWeightSpace σ w))
      (j : {j // exponentWeight (selectedStringWeight i (endpoint k) (full k) j) = w}),
    source.factor k w x j = coordinates k ⟨embed x.val, by
      exact (le_of_eq (intersection _)) x.property.1⟩ (selectedStringIndex (endpoint k i.left - endpoint k i.right) (full k) j.val)

end
end Schubert.RS.Representation

